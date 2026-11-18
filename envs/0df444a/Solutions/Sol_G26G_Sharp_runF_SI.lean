-- Prove2me | solution 1 for G26G.Sharp.runF_SI
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:29.704986+00:00
-- url     : https://prove2.me/submissions/d24ae131-c45b-4c14-ac59-37fbbde162ec

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.T31.Geo =====

/-! ### General tools for the Theorem 3.1 leaves -/

open MeasureTheory Matrix Set

namespace T31

/-! #### Quadratic forms of positive definite matrices -/

/-! #### Convex hulls of compact sets in finite dimension -/

section Hull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- combinations of `n` points of `K` -/
def combSet (K : Set E) (n : ℕ) : Set E :=
  (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ Set.univ.pi (fun _ => K))

lemma combSet_succ {K : Set E} {z₀ : E} (hz₀ : z₀ ∈ K) (n : ℕ) :
    combSet K n ⊆ combSet K (n + 1) := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  refine ⟨⟨Fin.snoc w 0, Fin.snoc z z₀⟩, ⟨⟨fun i => ?_, ?_⟩, fun i _ => ?_⟩, ?_⟩
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using hw.1 j
  · simp [Fin.sum_univ_castSucc, hw.2]
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hz₀
    · simpa using hz j (mem_univ _)
  · simp [Fin.sum_univ_castSucc]

lemma combSet_mono {K : Set E} (hK : K.Nonempty) {k N : ℕ} (h : k ≤ N) :
    combSet K k ⊆ combSet K N := by
  obtain ⟨z₀, hz₀⟩ := hK
  induction N, h using Nat.le_induction with
  | base => exact le_rfl
  | succ N _ ih => exact ih.trans (combSet_succ hz₀ N)

lemma combSet_sub_hull (K : Set E) (n : ℕ) : combSet K n ⊆ convexHull ℝ K := by
  rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i (mem_univ _)))

variable [FiniteDimensional ℝ E]

lemma hull_sub_combSet (K : Set E) :
    convexHull ℝ K ⊆ combSet K (Module.finrank ℝ E + 1) := by
  intro x hx
  obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
  have hne : K.Nonempty := convexHull_nonempty_iff.1 ⟨x, hx⟩
  refine combSet_mono hne hcard ?_
  let σ := Fintype.equivFin ι
  refine ⟨⟨w ∘ σ.symm, z ∘ σ.symm⟩, ⟨⟨fun i => (hw0 _).le, ?_⟩, fun i _ => hzK ⟨_, rfl⟩⟩, ?_⟩
  · simpa [Function.comp] using (Equiv.sum_comp σ.symm w).trans hw1
  · simp only [Function.comp]
    rw [← hsum]
    exact Equiv.sum_comp σ.symm (fun i => w i • z i)

lemma isCompact_convexHull_of {K : Set E} (hK : IsCompact K) : IsCompact (convexHull ℝ K) := by
  have : convexHull ℝ K = combSet K (Module.finrank ℝ E + 1) :=
    (hull_sub_combSet K).antisymm (combSet_sub_hull K _)
  rw [this]
  refine IsCompact.image ((isCompact_stdSimplex ℝ (Fin _)).prod (isCompact_univ_pi fun _ => hK)) ?_
  fun_prop

end Hull

/-! #### Integrals against measures supported on a compact set -/

variable {d : ℕ}

lemma ae_mem {n : Measure (Fin d → ℝ)} {𝒜 : Set (Fin d → ℝ)} (hn : n 𝒜ᶜ = 0) :
    ∀ᵐ a ∂n, a ∈ 𝒜 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hn] with a ha
  simpa using ha

lemma integrable_cpt {F : Type*} [NormedAddCommGroup F] {n : Measure (Fin d → ℝ)}
    [IsFiniteMeasure n] {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hn : n 𝒜ᶜ = 0)
    {f : (Fin d → ℝ) → F} (hf : Continuous f) : Integrable f n := by
  obtain ⟨C, hC⟩ := h𝒜.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (by filter_upwards [ae_mem hn] with a ha using hC a ha)

/-! #### Discrete measures -/

section Disc

variable {ι : Type*} [Fintype ι]

/-- the discrete measure `∑ r_i δ_{x_i}` -/
noncomputable def disc (r : ι → ℝ) (x : ι → Fin d → ℝ) : Measure (Fin d → ℝ) :=
  ∑ i, ENNReal.ofReal (r i) • Measure.dirac (x i)

instance disc_finite (r : ι → ℝ) (x : ι → Fin d → ℝ) : IsFiniteMeasure (disc r x) := by
  refine ⟨?_⟩
  simp only [disc, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.2 fun i _ => ENNReal.ofReal_lt_top

end Disc

/-! #### The gauge of `𝒮 = Conv(𝒜 ∪ -𝒜)` dominates the sup norm -/

lemma Sset_nhds {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤) :
    IAFTRL.Sset 𝒜 ∈ nhds (0 : Fin d → ℝ) := by
  set S := IAFTRL.Sset 𝒜 with hSdef
  have hconv : Convex ℝ S := convex_convexHull ℝ _
  have hsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have h' : -(𝒜 ∪ -𝒜) = 𝒜 ∪ -𝒜 := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (𝒜 ∪ -𝒜) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have haff : affineSpan ℝ S = ⊤ := by
    obtain ⟨a₀, ha₀⟩ := hne
    have hSne : S.Nonempty := ⟨a₀, subset_convexHull ℝ _ (Or.inl ha₀)⟩
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hSne, eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun a ha => ?_
    have hpa : a ∈ S := subset_convexHull ℝ _ (Or.inl ha)
    have hna : -a ∈ S := subset_convexHull ℝ _ (Or.inr (by simpa using ha))
    have h2 := vsub_mem_vectorSpan ℝ hpa hna
    rw [vsub_eq_sub, sub_neg_eq_add] at h2
    have := Submodule.smul_mem _ (1 / 2 : ℝ) h2
    have e : (1 / 2 : ℝ) • (a + a) = a := by
      rw [← two_smul ℝ a, smul_smul]; norm_num
    rwa [e] at this
  obtain ⟨x, hx⟩ := (hconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hxn : S ∈ nhds x := mem_interior_iff_mem_nhds.1 hx
  have hx' : -x ∈ interior S := by
    rw [mem_interior_iff_mem_nhds]
    have : (fun y : Fin d → ℝ => -y) ⁻¹' S ∈ nhds (-x) :=
      continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hxn)
    exact Filter.mem_of_superset this fun y hy => by simpa using hsymm _ hy
  have h0 : (0 : Fin d → ℝ) ∈ interior S := by
    have := hconv.interior hx hx' (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using this
  exact mem_interior_iff_mem_nhds.1 h0

end T31


-- ===== Solutions.G2.Lex =====

/-! ### Lexicographic minimizers exist on compact sets -/

open Set IAFTRL

namespace G2L

variable {d : ℕ}

lemma lex_min_exists {M : Set (Fin d → ℝ)} (hM : IsCompact M) (hne : M.Nonempty) :
    ∃ b ∈ M, ∀ b' ∈ M, toLex b ≤ toLex b' := by
  have key : ∀ n : ℕ, ∃ b ∈ M, ∀ b' ∈ M, (∀ j : Fin d, j.val < n → b j = b' j) ∨
      ∃ i : Fin d, i.val < n ∧ (∀ j : Fin d, j < i → b j = b' j) ∧ b i < b' i := by
    intro n
    induction n with
    | zero =>
      obtain ⟨b, hb⟩ := hne
      exact ⟨b, hb, fun b' _ => Or.inl fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ n ih =>
      obtain ⟨b, hbM, hb⟩ := ih
      by_cases hnd : n < d
      · set M' := {b' ∈ M | ∀ j : Fin d, j.val < n → b' j = b j} with hM'
        have hM'c : IsCompact M' := by
          change IsCompact (M ∩ {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j})
          refine hM.inter_right ?_
          have : {b' : Fin d → ℝ | ∀ j : Fin d, j.val < n → b' j = b j} =
              ⋂ j : Fin d, ⋂ (_ : j.val < n), {b' | b' j = b j} := by
            ext b'; simp
          rw [this]
          exact isClosed_iInter fun j => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply j) continuous_const
        have hM'ne : M'.Nonempty := ⟨b, hbM, fun _ _ => rfl⟩
        obtain ⟨bs, ⟨hbsM, hbsb⟩, hmin⟩ :=
          hM'c.exists_isMinOn hM'ne (continuous_apply (⟨n, hnd⟩ : Fin d)).continuousOn
        refine ⟨bs, hbsM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · have hb'M' : b' ∈ M' := ⟨hb'M, fun j hj => (hA j hj).symm⟩
          have hle : bs ⟨n, hnd⟩ ≤ b' ⟨n, hnd⟩ := hmin hb'M'
          rcases hle.lt_or_eq with hlt | heq
          · refine Or.inr ⟨⟨n, hnd⟩, Nat.lt_succ_self n, fun j hj => ?_, hlt⟩
            have hj' : j.val < n := hj
            rw [hbsb j hj', hA j hj']
          · refine Or.inl fun j hj => ?_
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
            · rw [hbsb j hj', hA j hj']
            · have : j = ⟨n, hnd⟩ := Fin.ext hj'
              rw [this, heq]
        · refine Or.inr ⟨i, Nat.lt_succ_of_lt hi, fun j hj => ?_, ?_⟩
          · have hj' : j.val < n := lt_trans hj hi
            rw [hbsb j hj', hpre j hj]
          · rw [hbsb i hi]; exact hlt
      · refine ⟨b, hbM, fun b' hb'M => ?_⟩
        rcases hb b' hb'M with hA | ⟨i, hi, hpre, hlt⟩
        · exact Or.inl fun j _ => hA j (lt_of_lt_of_le j.isLt (not_lt.1 hnd))
        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hpre, hlt⟩
  obtain ⟨b, hbM, hb⟩ := key d
  refine ⟨b, hbM, fun b' hb'M => ?_⟩
  rcases hb b' hb'M with hA | ⟨i, -, hpre, hlt⟩
  · have : b = b' := funext fun j => hA j j.isLt
    rw [this]
  · exact le_of_lt ⟨i, hpre, hlt⟩

lemma lexMinimizer_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (v : Fin d → ℝ) : lexMinimizer ℬ v ∈ ℬ := by
  have hc : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v := by
    simp only [dotProduct]; fun_prop
  obtain ⟨b₀, hb₀, hmin⟩ := hℬ.exists_isMinOn hne hc.continuousOn
  set M := ℬ ∩ {b | b ⬝ᵥ v ≤ b₀ ⬝ᵥ v} with hM
  have hMc : IsCompact M := hℬ.inter_right (isClosed_le hc continuous_const)
  obtain ⟨b, ⟨hbℬ, hbv⟩, hlex⟩ := lex_min_exists hMc ⟨b₀, hb₀, show b₀ ⬝ᵥ v ≤ b₀ ⬝ᵥ v from le_refl _⟩
  have h : ∃ b ∈ ℬ, (∀ a ∈ ℬ, b ⬝ᵥ v ≤ a ⬝ᵥ v) ∧
      ∀ b' ∈ ℬ, (∀ a ∈ ℬ, b' ⬝ᵥ v ≤ a ⬝ᵥ v) → toLex b ≤ toLex b' :=
    ⟨b, hbℬ, fun a ha => le_trans hbv (hmin ha),
      fun b' hb' hb'min => hlex b' ⟨hb', hb'min b₀ hb₀⟩⟩
  unfold lexMinimizer
  rw [dif_pos h]
  exact (Classical.choose_spec h).1

lemma cand_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (m : ℕ) : cand ℬ e m ∈ ℬ :=
  lexMinimizer_mem hℬ hne _

lemma gref_mem {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) (hne : ℬ.Nonempty)
    (e : ℕ → Fin d → ℚ) (t : ℕ) (S : Fin d → ℝ) : gref ℬ e t S ∈ ℬ :=
  cand_mem hℬ hne e _

end G2L


-- ===== Solutions.G2.Meas =====

/-! ### Measurability of the reconstruction and of the exponential weights -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2M

variable {d : ℕ}

open Classical in
/-- Markov-ification of a measure -/
noncomputable def mk (ν : Measure (Fin d → ℝ)) : Measure (Fin d → ℝ) :=
  if ν univ = 1 then ν else Measure.dirac 0

lemma measurable_mk : Measurable (mk (d := d)) := by
  classical
  have hs : MeasurableSet {ν : Measure (Fin d → ℝ) | ν univ = 1} :=
    (Measure.measurable_coe MeasurableSet.univ) (measurableSet_singleton 1)
  exact Measurable.piecewise hs measurable_id measurable_const

instance mk_prob (ν : Measure (Fin d → ℝ)) : IsProbabilityMeasure (mk ν) := by
  unfold mk
  split_ifs with h
  · exact ⟨h⟩
  · infer_instance

lemma mk_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] : mk ν = ν := by
  unfold mk; rw [if_pos measure_univ]

/-- the Markov kernel `ν ↦ mk ν` -/
noncomputable def kmk : Kernel (Measure (Fin d → ℝ)) (Fin d → ℝ) :=
  ⟨mk, measurable_mk⟩

instance : IsMarkovKernel (kmk (d := d)) := ⟨fun ν => mk_prob ν⟩

/-- measurability of `ν ↦ ∫ f d(mk ν)` -/
lemma measurable_integral_mk {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    Measurable fun ν : Measure (Fin d → ℝ) => ∫ x, f x ∂(mk ν) := by
  have := (hf.stronglyMeasurable.comp_measurable
    (measurable_snd (α := Measure (Fin d → ℝ)) (β := Fin d → ℝ))).integral_kernel_prod_right'
    (κ := kmk (d := d))
  exact this.measurable

/-- the design matrix entries of `mk ν` -/
noncomputable def cM (ν : Measure (Fin d → ℝ)) : Fin d → Fin d → ℝ :=
  fun i j => ∫ x, x i * x j ∂(mk ν)

lemma measurable_cM : Measurable (cM (d := d)) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  exact measurable_integral_mk (by fun_prop)

/-- entries of the inverse of a matrix given by its entries -/
noncomputable def invE (A : Fin d → Fin d → ℝ) : Fin d → Fin d → ℝ :=
  fun i j => (Matrix.of A)⁻¹ i j

lemma measurable_invE : Measurable (invE (d := d)) := by
  have hdet : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).det :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_det
  have hadj : Continuous fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate :=
    (continuous_id (X := Matrix (Fin d) (Fin d) ℝ)).matrix_adjugate
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
  have : (fun A : Fin d → Fin d → ℝ => invE A i j) =
      fun A => ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    funext A
    simp only [invE, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [this]
  have h1 : Measurable fun A : Fin d → Fin d → ℝ => (Matrix.of A).adjugate i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp hadj)).measurable
  exact (hdet.measurable.inv).mul h1

/-- the reconstruction vector `v_x(ν) = M(ν)⁻¹ x` computed from `mk ν` -/
noncomputable def V (ν : Measure (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => ∑ j, invE (cM ν) i j * x j

lemma measurable_V : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => V z.1 z.2 := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable fun z : Measure (Fin d → ℝ) × (Fin d → ℝ) => invE (cM z.1) i j :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_invE.comp (measurable_cM.comp measurable_fst)))
  exact h1.mul ((measurable_pi_apply j).comp measurable_snd)

lemma measurable_V_comp {α : Type*} {mα : MeasurableSpace α} {f : α → Measure (Fin d → ℝ)}
    {g : α → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => V (f a) (g a) := by
  have h2 := (measurable_V (d := d)).comp (hf.prodMk hg)
  convert h2 using 1
  funext a
  simp only [Function.comp_apply]

lemma cM_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] :
    Matrix.of (cM ν) = IAFTRL.designMat ν := by
  ext i j; simp [cM, IAFTRL.designMat, mk_eq]

lemma V_eq (ν : Measure (Fin d → ℝ)) [IsProbabilityMeasure ν] (x : Fin d → ℝ) :
    V ν x = IAFTRL.gv ν x := by
  funext i
  simp only [V, IAFTRL.gv, IAFTRL.gM, invE, ← cM_eq ν, Matrix.mulVec, dotProduct]

end G2M


-- ===== Solutions.G2.Law =====

/-! ### Joint law of a sub-σ-algebra measurable statistic and a conditionally distributed variable -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace G2W

variable {Ω : Type*} {G : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
  [IsProbabilityMeasure P] (hG : G ≤ mΩ)
  {𝒵 : Type*} [MeasurableSpace 𝒵] {Z : Ω → 𝒵} (hZ : Measurable[G] Z)
  {E : Type*} [MeasurableSpace E] {X : Ω → E} (hX : Measurable X)
  (κ : Kernel 𝒵 E) [IsMarkovKernel κ]
  (hlaw : ∀ s, MeasurableSet s →
    P[(X ⁻¹' s).indicator (fun _ => (1 : ℝ)) | G] =ᵐ[P] fun ω => (κ (Z ω) s).toReal)
include hG hZ hX hlaw

theorem law_eq : P.map (fun ω => (Z ω, X ω)) = (P.map Z) ⊗ₘ κ := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZm.aemeasurable
  haveI : IsProbabilityMeasure (P.map fun ω => (Z ω, X ω)) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ (by simp)
  rintro _ ⟨B, hB, s, hs, rfl⟩
  rw [Measure.map_apply hpair (hB.prod hs), Measure.compProd_apply_prod hB hs,
    setLIntegral_map hB (κ.measurable_coe hs) hZm]
  have hZB : MeasurableSet[G] (Z ⁻¹' B) := hZ hB
  have hpre : (fun ω => (Z ω, X ω)) ⁻¹' (B ×ˢ s) = Z ⁻¹' B ∩ X ⁻¹' s := by ext; simp
  rw [hpre]
  have hint : Integrable ((X ⁻¹' s).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hs)
  have h1 := setIntegral_condExp hG hint hZB
  rw [setIntegral_congr_ae (hG _ hZB) (by filter_upwards [hlaw s hs] with ω hω _ using hω)] at h1
  -- both sides as real numbers
  have hL : ∫ ω in Z ⁻¹' B, (X ⁻¹' s).indicator (fun _ => (1 : ℝ)) ω ∂P =
      P.real (Z ⁻¹' B ∩ X ⁻¹' s) := by
    rw [integral_indicator (hX hs), Measure.restrict_restrict (hX hs), setIntegral_const,
      smul_eq_mul, mul_one, Set.inter_comm]
  have hR : ∫ ω in Z ⁻¹' B, (κ (Z ω) s).toReal ∂P =
      (∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P).toReal := by
    exact integral_toReal (f := fun ω => κ (Z ω) s) ((κ.measurable_coe hs).comp hZm).aemeasurable
      (ae_of_all _ fun ω => measure_lt_top _ _)
  rw [hL, hR] at h1
  have hfin : ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≠ ∞ := by
    refine ne_top_of_le_ne_top (measure_ne_top (P.restrict (Z ⁻¹' B)) univ) ?_
    calc ∫⁻ ω in Z ⁻¹' B, κ (Z ω) s ∂P ≤ ∫⁻ _ in Z ⁻¹' B, 1 ∂P :=
          lintegral_mono fun ω => prob_le_one
      _ = (P.restrict (Z ⁻¹' B)) univ := by simp
  rw [measureReal_def] at h1
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hfin).1 h1.symm

theorem integral_law {F : 𝒵 × E → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Z ω, X ω)) P) :
    ∫ ω, F (Z ω, X ω) ∂P = ∫ ω, ∫ x, F (Z ω, x) ∂(κ (Z ω)) ∂P := by
  have hZm : Measurable Z := hZ.mono hG le_rfl
  have hpair : Measurable fun ω => (Z ω, X ω) := hZm.prodMk hX
  have hlawe := law_eq P hG hZ hX κ hlaw
  have hFi' : Integrable F ((P.map Z) ⊗ₘ κ) := by
    rw [← hlawe]
    exact (integrable_map_measure hF.aestronglyMeasurable hpair.aemeasurable).2 hFi
  rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable, hlawe,
    Measure.integral_compProd hFi',
    integral_map hZm.aemeasurable (hF.integral_kernel_prod_right').aestronglyMeasurable]

end G2W


-- ===== Solutions.G2.Run =====

/-! ### Basic facts about GIA-FTRL runs -/

open MeasureTheory ProbabilityTheory Set IAFTRL
open scoped ENNReal

namespace G2R

variable {d : ℕ}

/-! #### Geometry -/

lemma conv_eq {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) :
    convexHull ℝ 𝒜 = Kset ℬ :=
  (convexHull_min hgen.2 (convex_convexHull ℝ ℬ)).antisymm (convexHull_mono hgen.1)

lemma abs_dot_le_one {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IsGenerator 𝒜 ℬ)
    {θ : Fin d → ℝ} (hθ : setNorm 𝒜 θ ≤ 1) {x : Fin d → ℝ} (hx : x ∈ Kset ℬ) :
    |x ⬝ᵥ θ| ≤ 1 := by
  rw [← conv_eq hgen] at hx
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ θ| := by
    simp only [dotProduct]; fun_prop
  have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} := by
    have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ θ) :=
      ⟨fun x y => add_dotProduct x y θ, fun c x => smul_dotProduct c x θ⟩
    have : {x : Fin d → ℝ | |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ} =
        {w | w ⬝ᵥ θ ≤ setNorm 𝒜 θ} ∩ {w | -setNorm 𝒜 θ ≤ w ⬝ᵥ θ} := by
      ext x; simp [abs_le, and_comm]
    rw [this]
    exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
  have := convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩) hcvx hx
  exact le_trans (show |x ⬝ᵥ θ| ≤ setNorm 𝒜 θ from this) hθ

lemma Kset_compact {ℬ : Set (Fin d → ℝ)} (hℬ : IsCompact ℬ) : IsCompact (Kset ℬ) :=
  T31.isCompact_convexHull_of hℬ

lemma span_B {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : Submodule.span ℝ ℬ = ⊤ := by
  rw [eq_top_iff, ← hspan]
  refine Submodule.span_le.2 fun a ha => ?_
  have : convexHull ℝ ℬ ⊆ Submodule.span ℝ ℬ :=
    convexHull_min Submodule.subset_span (Submodule.span ℝ ℬ).convex
  exact this (hgen.2 ha)

lemma B_nonempty {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) : ℬ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have := span_B hgen hspan
  rw [h, Submodule.span_empty] at this
  have hne : (Pi.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) ∈ (⊤ : Submodule ℝ (Fin d → ℝ)) := trivial
  rw [← this, Submodule.mem_bot] at hne
  have := congrFun hne ⟨0, hd⟩
  simp at this

/-- the gauge of `𝒮` is at most `2` on differences of points of `𝒦` -/
lemma sNorm_sub_le {𝒜 ℬ : Set (Fin d → ℝ)} (hd : 1 ≤ d) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) {u w : Fin d → ℝ} (hu : u ∈ Kset ℬ) (hw : w ∈ Kset ℬ) :
    sNorm ℬ (u - w) ≤ 2 := by
  have hBne := B_nonempty hd hgen hspan
  have habs : Absorbent ℝ (Sset ℬ) := absorbent_nhds_zero (T31.Sset_nhds hBne (span_B hgen hspan))
  have hconv : Convex ℝ (Sset ℬ) := convex_convexHull ℝ _
  have hsub : Kset ℬ ⊆ Sset ℬ := convexHull_mono subset_union_left
  have hsymm : ∀ x ∈ Sset ℬ, -x ∈ Sset ℬ := by
    intro x hx
    have h' : -(ℬ ∪ -ℬ) = ℬ ∪ -ℬ := by
      ext y; simp only [Set.mem_neg, Set.mem_union, neg_neg]; tauto
    have : -x ∈ -convexHull ℝ (ℬ ∪ -ℬ) := by rw [Set.neg_mem_neg]; exact hx
    rw [← convexHull_neg, h'] at this
    exact this
  have h1 : gauge (Sset ℬ) u ≤ 1 := gauge_le_one_of_mem (hsub hu)
  have h2 : gauge (Sset ℬ) (-w) ≤ 1 := gauge_le_one_of_mem (hsymm _ (hsub hw))
  have := gauge_add_le hconv habs u (-w)
  rw [← sub_eq_add_neg] at this
  unfold sNorm
  linarith

lemma meas_dot' {α : Type*} {mα : MeasurableSpace α} {f g : α → Fin d → ℝ}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⬝ᵥ g a := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

/-! #### Runs -/

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma hist_mono {s t : ℕ} (h : s ≤ t) : R.hist s ≤ R.hist t := by
  unfold GRun.hist
  exact iSup₂_mono' fun i hi => ⟨i, lt_of_lt_of_le hi h, le_rfl⟩

lemma meas_hist_triple {s t : ℕ} (h : s < t) :
    Measurable[R.hist t] (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) := by
  refine Measurable.of_comap_le ?_
  exact le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s h

lemma meas_hist_Y {s t : ℕ} (hs : s < t) : Measurable[R.hist t] (R.Y s) := by
  refine Measurable.of_comap_le ?_
  have h1 : MeasurableSpace.comap (R.Y s) inferInstance ≤
      MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance := by
    have h2 : Measurable fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2 := measurable_snd.snd
    rw [show R.Y s = (fun z : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => z.2.2) ∘
      (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono h2.comap_le
  exact h1.trans (le_iSup₂ (f := fun s (_ : s < t) =>
    MeasurableSpace.comap (fun ω => (R.X s ω, R.A s ω, R.Y s ω)) inferInstance) s hs)

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsProbabilityMeasure (R.p t ω) :=
  (feas hR ht ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

lemma thetaHat_eq (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s : ℕ} (hs : s < T) (ω : Ω) :
    R.thetaHat s ω = R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := by
  haveI := p_prob hR hs ω
  rw [GRun.thetaHat, G2M.V_eq]

lemma meas_thetaHat (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {s t : ℕ} (hs : s < t) (ht : t ≤ T) :
    Measurable[R.hist t] (R.thetaHat s) := by
  have hp0 : Measurable[R.hist s] (R.p s) := (hR s (by omega)).2.1.1
  have hp : Measurable[R.hist t] (R.p s) := hp0.mono (hist_mono hs.le) le_rfl
  have htr := meas_hist_triple (R := R) hs
  have hX : Measurable[R.hist t] (R.X s) := measurable_fst.comp htr
  have hY : Measurable[R.hist t] (R.Y s) := meas_hist_Y hs
  have hV : Measurable[R.hist t] fun ω => G2M.V (R.p s ω) (R.X s ω) :=
    G2M.measurable_V_comp hp hX
  have hm : Measurable[R.hist t] fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) := hY.smul hV
  have : R.thetaHat s = fun ω => R.Y s ω • G2M.V (R.p s ω) (R.X s ω) :=
    funext (thetaHat_eq hR (by omega))
  rw [this]
  exact hm

lemma meas_cumEst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) :
    Measurable[R.hist t] (R.cumEst t) := by
  unfold GRun.cumEst
  exact Finset.measurable_sum _ fun s hs => meas_thetaHat hR (Finset.mem_range.1 hs) ht

lemma G_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.G t ≤ mΩ :=
  (hR t ht).1.2.2.2.2.1

lemma hist_le_G (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) : R.hist t ≤ R.G t :=
  (hR t ht).1.2.2.2.2.2.1

/-- the latent action lies in `𝒦` almost surely -/
lemma X_mem_K [IsProbabilityMeasure P] (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (hℬ : IsCompact ℬ)
    {t : ℕ} (ht : t < T) : ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ := by
  have hKc := (Kset_compact hℬ).isClosed.measurableSet.compl
  have hX : Measurable (R.X t) := (hR t ht).1.1
  have hlaw := (hR t ht).2.2.1 _ hKc
  have hGle := G_le hR ht
  have hint : Integrable ((R.X t ⁻¹' (Kset ℬ)ᶜ).indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hX hKc)
  have h1 := integral_condExp hGle (μ := P) (f := (R.X t ⁻¹' (Kset ℬ)ᶜ).indicator fun _ => (1 : ℝ))
  rw [integral_congr_ae hlaw] at h1
  simp only [p_supp hR ht, ENNReal.toReal_zero, integral_zero] at h1
  rw [integral_indicator (hX hKc), setIntegral_const, smul_eq_mul, mul_one] at h1
  have h0 : P (R.X t ⁻¹' (Kset ℬ)ᶜ) = 0 := by
    simp only [measureReal_restrict_apply_univ, measureReal_def] at h1
    exact (ENNReal.toReal_eq_zero_iff _).1 h1.symm |>.resolve_right (measure_ne_top _ _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  simpa using hω

end Run

/-! #### Deterministic range bounds -/

/-- the deterministic range recursion -/
noncomputable def rho (d : ℕ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d)

lemma gbeta_pos (hd : 1 ≤ d) (t : ℕ) : 0 < gbeta d t := by
  unfold gbeta
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  positivity

lemma gB_pos : 0 < gB d := by unfold gB; positivity

section Bounds

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝒜 ℬ : Set (Fin d → ℝ)}
  {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma v_bound (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (ω : Ω) {ρ : ℝ}
    (hS : ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ, |(u - w) ⬝ᵥ R.cumEst t ω| ≤ ρ) :
    ∀ x ∈ Kset ℬ, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) x| ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by
  intro x hX u hu w hw
  set S := R.cumEst t ω
  set b := gref ℬ e (t + 1) S
  have hbK : b ∈ Kset ℬ :=
    subset_convexHull ℝ ℬ (G2L.gref_mem hℬ (B_nonempty hd hgen hspan) e (t + 1) S)
  have hU := (feas hR ht ω).2.2.2.2.1
  have hβ := gbeta_pos hd (t + 1)
  have hB := gB_pos (d := d)
  have hUb : ∀ x ∈ Kset ℬ, gU ℬ e (t + 1) S x ≤ gbeta d (t + 1) + ρ / gB d := by
    intro y hy
    unfold gU
    have h1 : sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ 2 := sNorm_sub_le hd hgen hspan hy hbK
    have h2 : gZ ℬ e (t + 1) S y ≤ ρ := by
      unfold gZ
      refine max_le ?_ ?_
      · exact le_trans (abs_nonneg _) (hS y hy b hbK)
      · have := hS y hy b hbK
        rw [sub_dotProduct] at this
        exact le_trans (le_abs_self _) this
    have h3 : gbeta d (t + 1) / 2 * sNorm ℬ (y - gref ℬ e (t + 1) S) ≤ gbeta d (t + 1) := by
      nlinarith
    have h4 : gZ ℬ e (t + 1) S y / gB d ≤ ρ / gB d := div_le_div_of_nonneg_right h2 hB.le
    linarith
  have h1 := hU u hu x hX
  have h2 := hU w hw x hX
  have heq : (u - w) ⬝ᵥ gv (R.p t ω) x =
      (u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x := by
    simp only [sub_dotProduct]; ring
  rw [heq]
  calc |(u - b) ⬝ᵥ gv (R.p t ω) x - (w - b) ⬝ᵥ gv (R.p t ω) x|
      ≤ |(u - b) ⬝ᵥ gv (R.p t ω) x| + |(w - b) ⬝ᵥ gv (R.p t ω) x| :=
        abs_sub _ _
    _ ≤ gU ℬ e (t + 1) S u + gU ℬ e (t + 1) S w := add_le_add h1 h2
    _ ≤ 2 * (gbeta d (t + 1) + ρ / gB d) := by linarith [hUb u hu, hUb w hw]

lemma range_bound [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) :
    ∀ t, t ≤ T → ∀ᵐ ω ∂P, ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ R.cumEst t ω| ≤ rho d t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ae_of_all _ fun ω u _ w _ => by simp [GRun.cumEst, rho]
  | succ t ih =>
    intro ht
    have ht' : t < T := by omega
    filter_upwards [ih (by omega), X_mem_K hR hℬ ht'] with ω hS hX
    intro u hu w hw
    have hv := v_bound hd hℬ hgen hspan hR ht' ω hS (R.X t ω) hX u hu w hw
    have hY : |R.Y t ω| ≤ 1 := (hR t ht').2.2.2.2.1.1 ω
    have hsum : R.cumEst (t + 1) ω = R.cumEst t ω + R.thetaHat t ω := by
      simp [GRun.cumEst, Finset.sum_range_succ]
    rw [hsum, dotProduct_add]
    have hθ : |(u - w) ⬝ᵥ R.thetaHat t ω| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
      rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      calc |R.Y t ω| * |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)|
          ≤ 1 * (2 * (gbeta d (t + 1) + rho d t / gB d)) :=
            mul_le_mul hY hv (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc |(u - w) ⬝ᵥ R.cumEst t ω + (u - w) ⬝ᵥ R.thetaHat t ω|
        ≤ |(u - w) ⬝ᵥ R.cumEst t ω| + |(u - w) ⬝ᵥ R.thetaHat t ω| := abs_add_le _ _
      _ ≤ rho d t + 2 * (gbeta d (t + 1) + rho d t / gB d) := add_le_add (hS u hu w hw) hθ
      _ = rho d (t + 1) := rfl

/-- the almost sure bound on reconstruction differences in round `t` -/
lemma v_bound_ae [IsProbabilityMeasure P] (hd : 1 ≤ d) (hℬ : IsCompact ℬ)
    (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂P, R.X t ω ∈ Kset ℬ ∧ ∀ u ∈ Kset ℬ, ∀ w ∈ Kset ℬ,
      |(u - w) ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ 2 * (gbeta d (t + 1) + rho d t / gB d) := by
  filter_upwards [range_bound hd hℬ hgen hspan hR t ht.le, X_mem_K hR hℬ ht] with ω hS hX
  exact ⟨hX, v_bound hd hℬ hgen hspan hR ht ω hS (R.X t ω) hX⟩

end Bounds

end G2R


-- ===== Solutions.G2.Exp =====

/-! ### Conditional expectation identities along a GIA-FTRL run -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G2E

variable {d : ℕ}

/-- the statistic space `(p_t, S_t, θ_t)` -/
abbrev Zsp (d : ℕ) := Measure (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ)

/-- the conditional law kernel of the latent action -/
noncomputable def kZ : Kernel (Zsp d) (Fin d → ℝ) := G2M.kmk.comap Prod.fst measurable_fst

instance : IsMarkovKernel (kZ (d := d)) := by unfold kZ; infer_instance

/-- the dot product as a continuous bilinear map -/
noncomputable def dotB : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x ⬝ᵥ y) (fun x y z => add_dotProduct x y z)
    (fun c x y => smul_dotProduct c x y) (fun x y z => dotProduct_add x y z)
    (fun c x y => dotProduct_smul c x y)

noncomputable def dotL : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin d → ℝ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ dotB)

@[simp] lemma dotL_apply (x y : Fin d → ℝ) : dotL x y = x ⬝ᵥ y := rfl

lemma bil_designMat {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (a θ : Fin d → ℝ) :
    ∫ x, (a ⬝ᵥ x) * (x ⬝ᵥ θ) ∂ν = a ⬝ᵥ (designMat ν *ᵥ θ) := by
  have hI : ∀ i j, Integrable (fun x : Fin d → ℝ => a i * θ j * (x i * x j)) ν := fun i j =>
    T31.integrable_cpt hK hν (by fun_prop)
  have hfun : (fun x : Fin d → ℝ => (a ⬝ᵥ x) * (x ⬝ᵥ θ)) =
      fun x => ∑ i, ∑ j, a i * θ j * (x i * x j) := by
    funext x
    simp only [dotProduct, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfun, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  simp only [dotProduct, Matrix.mulVec, designMat, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]; ring

/-- the reconstruction identity `∫ (wᵀ M⁻¹ x)(xᵀ θ) p(dx) = wᵀ θ` -/
lemma recon {ν : Measure (Fin d → ℝ)} [IsProbabilityMeasure ν] {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hPD : (designMat ν).PosDef) (w θ : Fin d → ℝ) :
    ∫ x, (w ⬝ᵥ gv ν x) * (x ⬝ᵥ θ) ∂ν = w ⬝ᵥ θ := by
  have hdet : IsUnit (designMat ν).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit
  have h1 : ∀ x, w ⬝ᵥ gv ν x = (Matrix.vecMul w (designMat ν)⁻¹) ⬝ᵥ x := fun x => by
    rw [gv, gM, Matrix.dotProduct_mulVec]
  simp_rw [h1]
  rw [bil_designMat hK hν, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

section Run

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- the statistic `(p_t, S_t, θ_t)` -/
noncomputable def Zst (R : GRun d Ω) (t : ℕ) (ω : Ω) : Zsp d := (R.p t ω, R.cumEst t ω, R.θs t ω)

lemma kZ_Zst (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    kZ (Zst R t ω) = R.p t ω := by
  haveI := G2R.p_prob hR ht ω
  simp [kZ, Zst, G2M.kmk, G2M.mk_eq]

end Run

/-- the σ-algebra `G_t ∨ σ(X_t)` -/
def mX {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (R.X t) inferInstance

/-- the σ-algebra `G_t ∨ σ(X_t, A_t)` -/
def mXA {Ω : Type*} (R : GRun d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.G t ⊔ MeasurableSpace.comap (fun ω => (R.X t ω, R.A t ω)) inferInstance

section Ident

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

lemma integrable_A (hℬ : IsCompact ℬ) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) :
    Integrable (R.A t) P := by
  obtain ⟨C, hC⟩ := hℬ.exists_bound_of_continuousOn continuous_id.continuousOn
  exact Integrable.of_bound (hR t ht).1.2.1.aestronglyMeasurable C
    (ae_of_all _ fun ω => hC _ ((hR t ht).2.2.2.1.1 ω))

end Ident

end G2E


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the `ℓ¹` radius of `D` -/
noncomputable def rad1 (D : Set (Fin d → ℝ)) : ℝ := sSup ((fun u : Fin d → ℝ => ∑ i, |u i|) '' D)

lemma abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ (∑ i, |u i|) * ‖v‖ := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

lemma bdd_img (w : Fin d → ℝ) : BddAbove ((fun u => u ⬝ᵥ w) '' D) :=
  (hD.image (by simp only [dotProduct]; fun_prop)).bddAbove

lemma le_supp {u : Fin d → ℝ} (hu : u ∈ D) (w : Fin d → ℝ) : u ⬝ᵥ w ≤ supp D w :=
  le_csSup (bdd_img hD w) ⟨u, hu, rfl⟩

lemma supp_mem (hne : D.Nonempty) (w : Fin d → ℝ) : ∃ u ∈ D, u ⬝ᵥ w = supp D w := by
  have hc : IsCompact ((fun u => u ⬝ᵥ w) '' D) :=
    hD.image (by simp only [dotProduct]; fun_prop)
  obtain ⟨u, hu, he⟩ := hc.sSup_mem (hne.image _)
  exact ⟨u, hu, he⟩

lemma le_rad1 {u : Fin d → ℝ} (hu : u ∈ D) : ∑ i, |u i| ≤ rad1 D :=
  le_csSup (hD.image (by fun_prop)).bddAbove ⟨u, hu, rfl⟩

lemma supp_sub_le (hne : D.Nonempty) (w w' : Fin d → ℝ) :
    supp D w - supp D w' ≤ rad1 D * ‖w - w'‖ := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne w
  have h1 := le_supp hD hu w'
  have h2 := abs_dot_le u (w - w')
  have h3 : (∑ i, |u i|) * ‖w - w'‖ ≤ rad1 D * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right (le_rad1 hD hu) (norm_nonneg _)
  rw [dotProduct_sub] at h2
  have := (abs_le.1 h2).2
  linarith

lemma rad1_nonneg (hne : D.Nonempty) : 0 ≤ rad1 D := by
  obtain ⟨u, hu⟩ := hne
  exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (le_rad1 hD hu)

lemma supp_lip (hne : D.Nonempty) : LipschitzWith (Real.toNNReal (rad1 D)) (supp D) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (rad1_nonneg hD hne)]
  refine abs_le.2 ⟨?_, supp_sub_le hD hne w w'⟩
  have := supp_sub_le hD hne w' w
  rw [norm_sub_rev] at this
  linarith

lemma supp_cont (hne : D.Nonempty) : Continuous (supp D) := (supp_lip hD hne).continuous

lemma negMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    -(u ⬝ᵥ V + c) ≤ negMax D V c := by
  have := le_supp hD hu (-V)
  rw [dotProduct_neg] at this
  unfold negMax; linarith

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma negMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => negMax D (V ω) (c ω) := by
  have h := (negMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.RunCE =====

/-! ### Conditional moments of the loss estimates given the pre-action σ-algebra -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix
open scoped ENNReal

namespace G26R

variable {d : ℕ}

/-- the statistic `(p_t, θ_t, φ)` -/
abbrev Zsp (d : ℕ) := Measure (Fin d → ℝ) × (Fin d → ℝ) × ℝ

/-- the conditional law kernel of the latent action on the augmented statistic -/
noncomputable def kφ : Kernel (Zsp d) (Fin d → ℝ) := G2M.kmk.comap Prod.fst measurable_fst

instance : IsMarkovKernel (kφ (d := d)) := by unfold kφ; infer_instance

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- the augmented statistic -/
noncomputable def Zφ (R : GRun d Ω) (t : ℕ) (φ : Ω → ℝ) (ω : Ω) : Zsp d :=
  (R.p t ω, R.θs t ω, φ ω)

lemma meas_Zφ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) {φ : Ω → ℝ}
    (hφ : Measurable[R.G t] φ) : Measurable[R.G t] (Zφ R t φ) := by
  have hhG := G2R.hist_le_G hR ht
  have hp : Measurable[R.G t] (R.p t) := ((hR t ht).2.1.1).mono hhG le_rfl
  have hθ : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.2.1
  exact hp.prodMk (hθ.prodMk hφ)

lemma kφ_Zφ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (φ : Ω → ℝ) (ω : Ω) :
    kφ (Zφ R t φ ω) = R.p t ω := by
  haveI := G2R.p_prob hR ht ω
  simp [kφ, Zφ, G2M.kmk, G2M.mk_eq]

lemma int_law_φ (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) {φ : Ω → ℝ}
    (hφ : Measurable[R.G t] φ) {F : Zsp d × (Fin d → ℝ) → ℝ} (hF : StronglyMeasurable F)
    (hFi : Integrable (fun ω => F (Zφ R t φ ω, R.X t ω)) P) :
    ∫ ω, F (Zφ R t φ ω, R.X t ω) ∂P = ∫ ω, ∫ x, F (Zφ R t φ ω, x) ∂(R.p t ω) ∂P := by
  have hlaw : ∀ s, MeasurableSet s → P[(R.X t ⁻¹' s).indicator (fun _ => (1 : ℝ)) | R.G t] =ᵐ[P]
      fun ω => (kφ (Zφ R t φ ω) s).toReal := by
    intro s hs
    simp_rw [kφ_Zφ hR ht]
    exact (hR t ht).2.2.1 s hs
  rw [G2W.integral_law P (G2R.G_le hR ht) (meas_Zφ hR ht hφ) (hR t ht).1.1 kφ hlaw hF hFi]
  simp_rw [kφ_Zφ hR ht]

/-- **unbiasedness against a history-measurable test function** -/
lemma unbiased_φ (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (w : Fin d → ℝ) {cw : ℝ} (hw : ∀ᵐ ω ∂P, |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw)
    {φ : Ω → ℝ} (hφ : Measurable[R.G t] φ) (hφb : ∀ ω, |φ ω| ≤ 1) :
    Integrable (fun ω => φ ω * (w ⬝ᵥ R.thetaHat t ω)) P ∧
    ∫ ω, φ ω * (w ⬝ᵥ R.thetaHat t ω) ∂P = ∫ ω, φ ω * (w ⬝ᵥ R.θs t ω) ∂P := by
  obtain ⟨⟨hX, hA, hY, hθ, hGle, -, hθG, -⟩, -, -, ⟨hAB, hAc⟩, ⟨hYb, hYc⟩, hθn⟩ := hR t ht
  have hKc := G2R.Kset_compact hℬ
  have hZ : Measurable[R.G t] (Zφ R t φ) := meas_Zφ hR ht hφ
  -- the scalar coefficient `c₁ = φ wᵀ v_X(p)`
  set F1 : Zsp d × (Fin d → ℝ) → ℝ := fun z => z.1.2.2 * (w ⬝ᵥ G2M.V z.1.1 z.2) with hF1
  have hF1m : Measurable F1 :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).mul
      (G2R.meas_dot' measurable_const
        (G2M.measurable_V_comp (measurable_fst.comp measurable_fst) measurable_snd))
  set c1 : Ω → ℝ := fun ω => F1 (Zφ R t φ ω, R.X t ω) with hc1
  have hc1eq : ∀ ω, c1 ω = φ ω * (w ⬝ᵥ gv (R.p t ω) (R.X t ω)) := fun ω => by
    haveI := G2R.p_prob hR ht ω
    simp only [hc1, hF1, Zφ, G2M.V_eq]
  have hc1b : ∀ᵐ ω ∂P, |c1 ω| ≤ max cw 0 := by
    filter_upwards [hw] with ω hω
    rw [hc1eq, abs_mul]
    calc |φ ω| * |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ 1 * max cw 0 :=
          mul_le_mul (hφb ω) (hω.trans (le_max_left _ _)) (abs_nonneg _) zero_le_one
      _ = max cw 0 := one_mul _
  set cb := max cw 0 with hcb
  have hcb0 : 0 ≤ cb := le_max_right _ _
  -- measurability of `c₁` for the enlarged σ-algebras
  have hXmX : Measurable[G2E.mX R t] (R.X t) := Measurable.of_comap_le le_sup_right
  have hZmX : Measurable[G2E.mX R t] (Zφ R t φ) := hZ.mono le_sup_left le_rfl
  have hc1mX : Measurable[G2E.mX R t] c1 := hF1m.comp (hZmX.prodMk hXmX)
  have hXAm : Measurable[G2E.mXA R t] (fun ω => (R.X t ω, R.A t ω)) :=
    Measurable.of_comap_le le_sup_right
  have hc1mXA : Measurable[G2E.mXA R t] c1 :=
    hF1m.comp ((hZ.mono le_sup_left le_rfl).prodMk (measurable_fst.comp hXAm))
  have hmX : G2E.mX R t ≤ mΩ := sup_le hGle hX.comap_le
  have hmXA : G2E.mXA R t ≤ mΩ := sup_le hGle (hX.prodMk hA).comap_le
  have hc1m : Measurable c1 := hc1mX.mono hmX le_rfl
  -- integrability
  have hYi : Integrable (R.Y t) P := Integrable.of_bound hY.aestronglyMeasurable 1
    (ae_of_all _ fun ω => by simpa using hYb ω)
  have hc1Y : Integrable (c1 * R.Y t) P := by
    refine Integrable.of_bound (hc1m.mul hY).aestronglyMeasurable cb ?_
    filter_upwards [hc1b] with ω hω
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [hYb ω, abs_nonneg (c1 ω), abs_nonneg (R.Y t ω)]
  have hAθ : ∀ ω, |R.A t ω ⬝ᵥ R.θs t ω| ≤ 1 := fun ω =>
    G2R.abs_dot_le_one h𝒜 hgen (hθn ω) (subset_convexHull ℝ ℬ (hAB ω))
  have hc1A : Integrable (fun ω => G2E.dotL (c1 ω • R.θs t ω) (R.A t ω)) P := by
    refine Integrable.of_bound ?_ cb ?_
    · simp only [G2E.dotL_apply, smul_dotProduct, smul_eq_mul]
      exact (hc1m.mul (G2R.meas_dot' hθ hA)).aestronglyMeasurable
    · filter_upwards [hc1b] with ω hω
      simp only [G2E.dotL_apply, smul_dotProduct, smul_eq_mul, Real.norm_eq_abs, abs_mul]
      rw [dotProduct_comm]
      nlinarith [hAθ ω, abs_nonneg (c1 ω), abs_nonneg (R.A t ω ⬝ᵥ R.θs t ω)]
  -- step a: replace the feedback by its conditional mean
  have hstepa : ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
    have h := condExp_mul_of_stronglyMeasurable_left hc1mXA.stronglyMeasurable hc1Y hYi
    calc ∫ ω, c1 ω * R.Y t ω ∂P = ∫ ω, (c1 * R.Y t) ω ∂P := rfl
      _ = ∫ ω, P[c1 * R.Y t | G2E.mXA R t] ω ∂P := (integral_condExp hmXA).symm
      _ = ∫ ω, (c1 * P[R.Y t | G2E.mXA R t]) ω ∂P := integral_congr_ae h
      _ = ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hYc] with ω hω
          rw [Pi.mul_apply, show P[R.Y t | G2E.mXA R t] ω = R.A t ω ⬝ᵥ R.θs t ω from hω]
  -- step b: replace the physical action by the latent one
  have hstepb : ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P =
      ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
    have hf : StronglyMeasurable[G2E.mX R t] fun ω => c1 ω • R.θs t ω :=
      (hc1mX.smul (hθG.mono le_sup_left le_rfl)).stronglyMeasurable
    have h := condExp_bilin_of_stronglyMeasurable_left G2E.dotL hf hc1A
      (G2E.integrable_A hℬ hR ht)
    calc ∫ ω, c1 ω * (R.A t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (R.A t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
      _ = ∫ ω, P[fun ω => G2E.dotL (c1 ω • R.θs t ω) (R.A t ω) | G2E.mX R t] ω ∂P :=
          (integral_condExp hmX).symm
      _ = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (P[R.A t | G2E.mX R t] ω) ∂P := integral_congr_ae h
      _ = ∫ ω, G2E.dotL (c1 ω • R.θs t ω) (R.X t ω) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hAc] with ω hω
          rw [show P[R.A t | G2E.mX R t] ω = R.X t ω from hω]
      _ = ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P := by
          simp [smul_dotProduct, dotProduct_comm]
  -- step c: the conditional law of the latent action
  set F2 : Zsp d × (Fin d → ℝ) → ℝ := fun z => F1 z * (z.2 ⬝ᵥ z.1.2.1) with hF2
  have hF2m : Measurable F2 :=
    hF1m.mul (G2R.meas_dot' measurable_snd
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hF2i : Integrable (fun ω => F2 (Zφ R t φ ω, R.X t ω)) P := by
    refine Integrable.of_bound (hF2m.comp ((hZ.mono hGle le_rfl).prodMk hX)).aestronglyMeasurable
      cb ?_
    filter_upwards [hc1b, G2R.X_mem_K hR hℬ ht] with ω hω hXK
    have hXθ := G2R.abs_dot_le_one h𝒜 hgen (hθn ω) hXK
    simp only [hF2, Real.norm_eq_abs, abs_mul]
    have : |F1 (Zφ R t φ ω, R.X t ω)| ≤ cb := hω
    simp only [Zφ] at this ⊢
    nlinarith [abs_nonneg (F1 ((R.p t ω, R.θs t ω, φ ω), R.X t ω)),
      abs_nonneg (R.X t ω ⬝ᵥ R.θs t ω)]
  have hstepc := int_law_φ hR ht hφ hF2m.stronglyMeasurable hF2i
  -- step d: the reconstruction identity
  have hstepd : ∀ ω, ∫ x, F2 (Zφ R t φ ω, x) ∂(R.p t ω) = φ ω * (w ⬝ᵥ R.θs t ω) := by
    intro ω
    haveI := G2R.p_prob hR ht ω
    have hPD := (G2R.feas hR ht ω).2.2.2.1
    have : (fun x => F2 (Zφ R t φ ω, x)) =
        fun x => φ ω * ((w ⬝ᵥ gv (R.p t ω) x) * (x ⬝ᵥ R.θs t ω)) := by
      funext x; simp only [hF2, hF1, Zφ, G2M.V_eq]; ring
    rw [this, integral_const_mul, G2E.recon hKc (G2R.p_supp hR ht ω) hPD]
  -- assemble
  have hθhat : ∀ ω, φ ω * (w ⬝ᵥ R.thetaHat t ω) = c1 ω * R.Y t ω := fun ω => by
    rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, hc1eq]; ring
  refine ⟨?_, ?_⟩
  · simp_rw [hθhat]; exact hc1Y
  · simp_rw [hθhat]
    rw [hstepa, hstepb]
    have : ∫ ω, c1 ω * (R.X t ω ⬝ᵥ R.θs t ω) ∂P = ∫ ω, F2 (Zφ R t φ ω, R.X t ω) ∂P := rfl
    rw [this, hstepc]
    exact integral_congr_ae (ae_of_all _ hstepd)

end G26R

namespace G26R

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- a conditional expectation is dominated by a measurable function dominating it on all sets -/
lemma condExp_le_of_setIntegral {G : ℕ → MeasurableSpace Ω} {t : ℕ} (hG : G t ≤ mΩ)
    {f h : Ω → ℝ} (hf : Integrable f μ) (hh : Integrable h μ) (hhm : StronglyMeasurable[G t] h)
    (hle : ∀ s, MeasurableSet[G t] s → ∫ ω in s, f ω ∂μ ≤ ∫ ω in s, h ω ∂μ) :
    μ[f | G t] ≤ᵐ[μ] h := by
  have h1 : Integrable (μ[f | G t]) (μ.trim hG) := integrable_condExp.trim hG stronglyMeasurable_condExp
  have h2 : Integrable h (μ.trim hG) := hh.trim hG hhm
  have h3 : μ[f | G t] ≤ᵐ[μ.trim hG] h := by
    refine ae_le_of_forall_setIntegral_le h1 h2 fun s hs _ => ?_
    rw [← setIntegral_trim hG stronglyMeasurable_condExp hs, ← setIntegral_trim hG hhm hs,
      setIntegral_condExp hG hf hs]
    exact hle s hs
  exact ae_of_ae_trim hG h3

/-- characterization of a conditional expectation by its set integrals -/
lemma condExp_eq_of_setIntegral {G : ℕ → MeasurableSpace Ω} {t : ℕ} (hG : G t ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hgm : StronglyMeasurable[G t] g)
    (heq : ∀ s, MeasurableSet[G t] s → ∫ ω in s, f ω ∂μ = ∫ ω in s, g ω ∂μ) :
    μ[f | G t] =ᵐ[μ] g := by
  have := isFiniteMeasure_trim (μ := μ) hG
  exact (ae_eq_condExp_of_forall_setIntegral_eq hG hf (fun s _ _ => hg.integrableOn)
    (fun s hs _ => (heq s hs).symm) hgm.aestronglyMeasurable).symm

end G26R

namespace G26R

variable {d : ℕ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {T : ℕ} {R : GRun d Ω}

/-- **conditional unbiasedness**: `E[wᵀθ̂_t | G_t] = wᵀθ_t` -/
lemma cond_mean (hd : 1 ≤ d) (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hspan : Submodule.span ℝ 𝒜 = ⊤) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T)
    (w : Fin d → ℝ) {cw : ℝ} (hw : ∀ᵐ ω ∂P, |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw)
    {cθ : ℝ} (hwθ : ∀ ω, |w ⬝ᵥ R.θs t ω| ≤ cθ) :
    P[fun ω => w ⬝ᵥ R.thetaHat t ω | R.G t] =ᵐ[P] fun ω => w ⬝ᵥ R.θs t ω := by
  have hGle := G2R.G_le hR ht
  have hθG : Measurable[R.G t] (R.θs t) := (hR t ht).1.2.2.2.2.2.2.1
  have hgm : StronglyMeasurable[R.G t] (fun ω => w ⬝ᵥ R.θs t ω) :=
    (G2R.meas_dot' measurable_const hθG).stronglyMeasurable
  have hgi : Integrable (fun ω => w ⬝ᵥ R.θs t ω) P :=
    Integrable.of_bound (hgm.mono hGle).aestronglyMeasurable cθ
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hwθ ω)
  have hfi : Integrable (fun ω => w ⬝ᵥ R.thetaHat t ω) P := by
    have := (unbiased_φ hd h𝒜 hℬ hgen hspan hR ht w hw (φ := fun _ => 1) measurable_const
      (fun _ => by simp)).1
    simpa using this
  refine condExp_eq_of_setIntegral (G := R.G) hGle hfi hgi hgm fun s hs => ?_
  have hsm : MeasurableSet s := hGle _ hs
  have hφm : Measurable[R.G t] (s.indicator fun _ => (1 : ℝ)) :=
    measurable_const.indicator hs
  have h := (unbiased_φ hd h𝒜 hℬ hgen hspan hR ht w hw hφm (fun ω => by
    simp only [Set.indicator]; split_ifs <;> simp)).2
  rw [← integral_indicator hsm, ← integral_indicator hsm]
  convert h using 2 <;> (funext ω; simp only [Set.indicator]; split_ifs <;> simp)

/-- **conditional second moment**: `E[(wᵀθ̂_t)² | G_t] ≤ h` whenever `∫ (wᵀv_x)² dp_t ≤ h` -/
lemma cond_sec (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ}
    (ht : t < T) (w : Fin d → ℝ) {cw : ℝ} (hw : ∀ᵐ ω ∂P, |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw)
    {h : Ω → ℝ} (hhm : StronglyMeasurable[R.G t] h) (hhi : Integrable h P)
    (hq : ∀ᵐ ω ∂P, ∫ x, (w ⬝ᵥ gv (R.p t ω) x) ^ 2 ∂(R.p t ω) ≤ h ω) :
    P[fun ω => (w ⬝ᵥ R.thetaHat t ω) ^ 2 | R.G t] ≤ᵐ[P] h := by
  obtain ⟨⟨hX, hA, hY, hθ, hGle, -, hθG, -⟩, -, -, -, ⟨hYb, -⟩, -⟩ := hR t ht
  have hvm : Measurable fun ω => w ⬝ᵥ gv (R.p t ω) (R.X t ω) := by
    have hp : Measurable (R.p t) :=
      ((hR t ht).2.1.1).mono ((G2R.hist_le_G hR ht).trans hGle) le_rfl
    have : (fun ω => w ⬝ᵥ gv (R.p t ω) (R.X t ω)) = fun ω => w ⬝ᵥ G2M.V (R.p t ω) (R.X t ω) := by
      funext ω; haveI := G2R.p_prob hR ht ω; rw [G2M.V_eq]
    rw [this]
    exact G2R.meas_dot' measurable_const (G2M.measurable_V_comp hp hX)
  have hθhat : ∀ ω, w ⬝ᵥ R.thetaHat t ω = R.Y t ω * (w ⬝ᵥ gv (R.p t ω) (R.X t ω)) := fun ω => by
    rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul]
  have hfm : Measurable fun ω => (w ⬝ᵥ R.thetaHat t ω) ^ 2 := by
    simp_rw [hθhat]; exact (hY.mul hvm).pow_const 2
  have hfi : Integrable (fun ω => (w ⬝ᵥ R.thetaHat t ω) ^ 2) P := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (cw ^ 2) ?_
    filter_upwards [hw] with ω hω
    rw [Real.norm_eq_abs, abs_pow, hθhat, abs_mul]
    have := hYb ω
    have h1 : |R.Y t ω| * |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ≤ cw :=
      le_trans (mul_le_of_le_one_left (abs_nonneg _) this) hω
    exact pow_le_pow_left₀ (by positivity) h1 2
  refine condExp_le_of_setIntegral (G := R.G) hGle hfi hhi hhm fun s hs => ?_
  have hsm : MeasurableSet s := hGle _ hs
  have hφm : Measurable[R.G t] (s.indicator fun _ => (1 : ℝ)) := measurable_const.indicator hs
  set φ := s.indicator fun _ => (1 : ℝ) with hφ
  have hφ01 : ∀ ω, 0 ≤ φ ω ∧ φ ω ≤ 1 := fun ω => by
    simp only [φ, Set.indicator]; split_ifs <;> simp
  -- the law step
  set F : Zsp d × (Fin d → ℝ) → ℝ := fun z => z.1.2.2 * (w ⬝ᵥ G2M.V z.1.1 z.2) ^ 2 with hF
  have hFm : Measurable F :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).mul
      ((G2R.meas_dot' measurable_const
        (G2M.measurable_V_comp (measurable_fst.comp measurable_fst) measurable_snd)).pow_const 2)
  have hFZ : ∀ ω, F (Zφ R t φ ω, R.X t ω) = φ ω * (w ⬝ᵥ gv (R.p t ω) (R.X t ω)) ^ 2 := fun ω => by
    haveI := G2R.p_prob hR ht ω
    simp only [hF, Zφ, G2M.V_eq]
  have hFi : Integrable (fun ω => F (Zφ R t φ ω, R.X t ω)) P := by
    simp_rw [hFZ]
    refine Integrable.of_bound ((hφm.mono hGle le_rfl).mul (hvm.pow_const 2)).aestronglyMeasurable
      (cw ^ 2) ?_
    filter_upwards [hw] with ω hω
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |w ⬝ᵥ gv (R.p t ω) (R.X t ω)| ^ 2 ≤ cw ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hω 2
    have h2 : |φ ω| ≤ 1 := by rw [abs_of_nonneg (hφ01 ω).1]; exact (hφ01 ω).2
    nlinarith [abs_nonneg (φ ω), sq_nonneg |w ⬝ᵥ gv (R.p t ω) (R.X t ω)|]
  have hlaw := int_law_φ hR ht hφm hFm.stronglyMeasurable hFi
  have hinner : ∀ ω, ∫ x, F (Zφ R t φ ω, x) ∂(R.p t ω) =
      φ ω * ∫ x, (w ⬝ᵥ gv (R.p t ω) x) ^ 2 ∂(R.p t ω) := fun ω => by
    haveI := G2R.p_prob hR ht ω
    rw [← integral_const_mul]
    congr 1; funext x; simp only [hF, Zφ, G2M.V_eq]
  calc ∫ ω in s, (w ⬝ᵥ R.thetaHat t ω) ^ 2 ∂P
      = ∫ ω, φ ω * (w ⬝ᵥ R.thetaHat t ω) ^ 2 ∂P := by
        rw [← integral_indicator hsm]; congr 1; funext ω
        simp only [φ, Set.indicator]; split_ifs <;> simp
    _ ≤ ∫ ω, F (Zφ R t φ ω, R.X t ω) ∂P := by
        refine integral_mono_ae ?_ hFi ?_
        · exact hfi.bdd_mul (hφm.mono hGle le_rfl).aestronglyMeasurable
            (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 ω).1]; exact (hφ01 ω).2)
        · refine ae_of_all _ fun ω => ?_
          show φ ω * (w ⬝ᵥ R.thetaHat t ω) ^ 2 ≤ F (Zφ R t φ ω, R.X t ω)
          rw [hFZ, hθhat, mul_pow]
          have := hYb ω
          have hY2 : R.Y t ω ^ 2 ≤ 1 := by
            rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) this
          exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) hY2) (hφ01 ω).1
    _ = ∫ ω, φ ω * ∫ x, (w ⬝ᵥ gv (R.p t ω) x) ^ 2 ∂(R.p t ω) ∂P := by
        rw [hlaw]; simp_rw [hinner]
    _ ≤ ∫ ω, φ ω * h ω ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun ω => ?_) ?_ ?_
        · exact mul_nonneg (hφ01 ω).1 (integral_nonneg fun x => sq_nonneg _)
        · exact hhi.bdd_mul (hφm.mono hGle le_rfl).aestronglyMeasurable
            (ae_of_all _ fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hφ01 ω).1]; exact (hφ01 ω).2)
        · filter_upwards [hq] with ω hω
          exact mul_le_mul_of_nonneg_left hω (hφ01 ω).1
    _ = ∫ ω in s, h ω ∂P := by
        rw [← integral_indicator hsm]; congr 1; funext ω
        simp only [φ, Set.indicator]; split_ifs <;> simp

end G26R

namespace G26R

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- conditional moments of a predictably shifted variable -/
lemma condExp_shift {G : ℕ → MeasurableSpace Ω} {t : ℕ} (hG : G t ≤ mΩ) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) (hgm : StronglyMeasurable[G t] g)
    {cg : ℝ} (hgb : ∀ ω, |g ω| ≤ cg) :
    (μ[fun ω => f ω + g ω | G t] =ᵐ[μ] fun ω => μ[f | G t] ω + g ω) ∧
    (μ[fun ω => (f ω + g ω) ^ 2 | G t] =ᵐ[μ]
      fun ω => μ[fun ω => f ω ^ 2 | G t] ω + 2 * g ω * μ[f | G t] ω + g ω ^ 2) := by
  have hgi : Integrable g μ := Integrable.of_bound (hgm.mono hG).aestronglyMeasurable cg
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hgbd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ cg := ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb ω
  have hg2m : StronglyMeasurable[G t] fun ω => g ω ^ 2 := hgm.pow 2
  have hg2i : Integrable (fun ω => g ω ^ 2) μ :=
    Integrable.of_bound ((hgm.pow 2).mono hG).aestronglyMeasurable (cg ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb ω) 2)
  have hfg : Integrable (fun ω => 2 * g ω * f ω) μ := by
    have := hf.bdd_mul ((hgm.mono hG).aestronglyMeasurable) hgbd
    simpa [mul_assoc] using this.const_mul 2
  constructor
  · have h1 := condExp_add hf hgi (G t) (μ := μ)
    have h2 : μ[g | G t] = g := condExp_of_stronglyMeasurable hG hgm hgi
    filter_upwards [h1] with ω hω
    simp only [Pi.add_apply] at hω
    have e : (fun ω => f ω + g ω) = f + g := rfl
    rw [e, hω, h2]
  · have e : (fun ω => (f ω + g ω) ^ 2) =
        (fun ω => f ω ^ 2) + ((fun ω => 2 * g ω * f ω) + fun ω => g ω ^ 2) := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e]
    have h1 := condExp_add hf2 (hfg.add hg2i) (G t) (μ := μ)
    have h2 := condExp_add hfg hg2i (G t) (μ := μ)
    have h3 : μ[fun ω => g ω ^ 2 | G t] = fun ω => g ω ^ 2 := condExp_of_stronglyMeasurable hG hg2m hg2i
    have h4 : μ[fun ω => 2 * g ω * f ω | G t] =ᵐ[μ] fun ω => 2 * g ω * μ[f | G t] ω := by
      have hm : StronglyMeasurable[G t] fun ω => 2 * g ω := hgm.const_mul 2
      have e0 : (fun ω => 2 * g ω * f ω) = (fun ω => 2 * g ω) * f := rfl
      rw [e0]
      have := condExp_mul_of_stronglyMeasurable_left hm (by rw [← e0]; exact hfg) hf
      filter_upwards [this] with ω hω
      rw [hω]; rfl
    filter_upwards [h1, h2, h4] with ω e1 e2 e4
    simp only [Pi.add_apply] at e1 e2
    rw [e1, e2, e4, h3]
    ring

end G26R


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

/-- the negative maximum of `X(u) = (u − a*)ᵀS` on `K` -/
noncomputable def NK (ℬ : Set (Fin d → ℝ)) (astar S : Fin d → ℝ) : ℝ :=
  negMax (Kset ℬ) S (-(astar ⬝ᵥ S))

lemma fzK (u astar S : Fin d → ℝ) : u ⬝ᵥ S + -(astar ⬝ᵥ S) = (u - astar) ⬝ᵥ S := by
  rw [sub_dotProduct]; ring

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

lemma NK_facts {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) (S : Fin d → ℝ) {u : Fin d → ℝ}
    (hu : u ∈ Kset ℬ) :
    0 ≤ NK ℬ astar S ∧ 0 ≤ (u - astar) ⬝ᵥ S + NK ℬ astar S := by
  have hKc := G2R.Kset_compact hℬ
  have h1 := negMax_ge hKc haK S (-(astar ⬝ᵥ S))
  have h2 := negMax_ge hKc hu S (-(astar ⬝ᵥ S))
  rw [fzK] at h1 h2
  simp only [sub_self, zero_dotProduct, neg_zero] at h1
  unfold NK
  constructor <;> linarith

/-- the reference-relative gaps are dominated by the `a*`-relative field -/
lemma gZ_le {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) (t : ℕ) (S : Fin d → ℝ) {u : Fin d → ℝ}
    (hu : u ∈ Kset ℬ) :
    gZ ℬ e t S u ≤ (u - astar) ⬝ᵥ S + NK ℬ astar S ∧ gZ ℬ e t S astar ≤ NK ℬ astar S := by
  have hKc := G2R.Kset_compact hℬ
  have hBne := G2R.B_nonempty hd hgen hspan
  set b := gref ℬ e t S
  have hbK : b ∈ Kset ℬ := subset_convexHull ℝ ℬ (G2L.gref_mem hℬ hBne e t S)
  have hb := negMax_ge hKc hbK S (-(astar ⬝ᵥ S))
  rw [fzK] at hb
  obtain ⟨hN0, hNu⟩ := NK_facts hd hℬ hgen hspan haK S hu
  unfold gZ NK at *
  constructor
  · refine max_le hNu ?_
    have : u ⬝ᵥ S - b ⬝ᵥ S = (u - astar) ⬝ᵥ S - (b - astar) ⬝ᵥ S := by
      simp only [sub_dotProduct]; ring
    rw [this]; linarith
  · refine max_le hN0 ?_
    have : astar ⬝ᵥ S - b ⬝ᵥ S = -((b - astar) ⬝ᵥ S) := by simp only [sub_dotProduct]; ring
    rw [this]; linarith

/-- **update magnitude (G.153)** at a feasible law -/
lemma magK {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) {t : ℕ} {S : Fin d → ℝ}
    {p : Measure (Fin d → ℝ)} (hp : IsFeasible3_6 ℬ e (t + 1) S p) {x : Fin d → ℝ}
    (hx : x ∈ Kset ℬ) {u : Fin d → ℝ} (hu : u ∈ Kset ℬ) :
    |(u - astar) ⬝ᵥ gv p x| ≤
      2 * gbeta d (t + 1) + ((u - astar) ⬝ᵥ S + 2 * NK ℬ astar S) / gB d := by
  have hBne := G2R.B_nonempty hd hgen hspan
  set b := gref ℬ e (t + 1) S
  have hbK : b ∈ Kset ℬ := subset_convexHull ℝ ℬ (G2L.gref_mem hℬ hBne e (t + 1) S)
  have hU := hp.2.2.2.2.1
  have h1 := hU u hu x hx
  have h2 := hU astar haK x hx
  obtain ⟨hz1, hz2⟩ := gZ_le (e := e) hd hℬ hgen hspan haK (t + 1) S hu
  have hs1 := G2R.sNorm_sub_le hd hgen hspan hu hbK
  have hs2 := G2R.sNorm_sub_le hd hgen hspan haK hbK
  have hβ := G2R.gbeta_pos hd (t + 1)
  have hB := G2R.gB_pos (d := d)
  have hU1 : gU ℬ e (t + 1) S u ≤ gbeta d (t + 1) + ((u - astar) ⬝ᵥ S + NK ℬ astar S) / gB d := by
    unfold gU
    have : gbeta d (t + 1) / 2 * sNorm ℬ (u - b) ≤ gbeta d (t + 1) := by nlinarith
    have : gZ ℬ e (t + 1) S u / gB d ≤ ((u - astar) ⬝ᵥ S + NK ℬ astar S) / gB d :=
      div_le_div_of_nonneg_right hz1 hB.le
    linarith
  have hU2 : gU ℬ e (t + 1) S astar ≤ gbeta d (t + 1) + NK ℬ astar S / gB d := by
    unfold gU
    have : gbeta d (t + 1) / 2 * sNorm ℬ (astar - b) ≤ gbeta d (t + 1) := by nlinarith
    have : gZ ℬ e (t + 1) S astar / gB d ≤ NK ℬ astar S / gB d :=
      div_le_div_of_nonneg_right hz2 hB.le
    linarith
  have heq : (u - astar) ⬝ᵥ gv p x = (u - b) ⬝ᵥ gv p x - (astar - b) ⬝ᵥ gv p x := by
    simp only [sub_dotProduct]; ring
  rw [heq]
  have e2 : 2 * gbeta d (t + 1) + ((u - astar) ⬝ᵥ S + 2 * NK ℬ astar S) / gB d =
      (gbeta d (t + 1) + ((u - astar) ⬝ᵥ S + NK ℬ astar S) / gB d) +
        (gbeta d (t + 1) + NK ℬ astar S / gB d) := by ring
  rw [e2]
  exact (abs_sub _ _).trans (add_le_add (h1.trans hU1) (h2.trans hU2))

/-- **conditional second moment (G.154)** at a feasible law -/
lemma secK {astar : Fin d → ℝ} (haK : astar ∈ Kset ℬ) {t : ℕ} {S : Fin d → ℝ}
    {p : Measure (Fin d → ℝ)} (hp : IsFeasible3_6 ℬ e (t + 1) S p) {u : Fin d → ℝ}
    (hu : u ∈ Kset ℬ) :
    ∫ x, ((u - astar) ⬝ᵥ gv p x) ^ 2 ∂p ≤
      4 * gbeta d (t + 1) + 2 * ((u - astar) ⬝ᵥ S + 2 * NK ℬ astar S) ^ 2 /
        (gB d * ((t : ℝ) + 1)) := by
  haveI := hp.1
  have hKc := G2R.Kset_compact hℬ
  have hBne := G2R.B_nonempty hd hgen hspan
  set b := gref ℬ e (t + 1) S
  have hbK : b ∈ Kset ℬ := subset_convexHull ℝ ℬ (G2L.gref_mem hℬ hBne e (t + 1) S)
  have hW := hp.2.2.2.2.2.1
  have h1 := hW u hu
  have h2 := hW astar haK
  obtain ⟨hz1, hz2⟩ := gZ_le (e := e) hd hℬ hgen hspan haK (t + 1) S hu
  obtain ⟨hN0, hNu⟩ := NK_facts hd hℬ hgen hspan haK S hu
  have hs1 := G2R.sNorm_sub_le hd hgen hspan hu hbK
  have hs2 := G2R.sNorm_sub_le hd hgen hspan haK hbK
  have hβ := G2R.gbeta_pos hd (t + 1)
  have hB := G2R.gB_pos (d := d)
  have hx0 : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by positivity
  have hcont : Continuous fun x => gv p x := by
    unfold gv; exact (Matrix.mulVecLin (gM p)⁻¹).continuous_of_finiteDimensional
  have hi1 : Integrable (fun x => ((u - b) ⬝ᵥ gv p x) ^ 2) p :=
    T31.integrable_cpt hKc hp.2.1 (by simp only [dotProduct]; fun_prop)
  have hi2 : Integrable (fun x => ((astar - b) ⬝ᵥ gv p x) ^ 2) p :=
    T31.integrable_cpt hKc hp.2.1 (by simp only [dotProduct]; fun_prop)
  have hi0 : Integrable (fun x => ((u - astar) ⬝ᵥ gv p x) ^ 2) p :=
    T31.integrable_cpt hKc hp.2.1 (by simp only [dotProduct]; fun_prop)
  have hpt : ∀ x, ((u - astar) ⬝ᵥ gv p x) ^ 2 ≤
      2 * ((u - b) ⬝ᵥ gv p x) ^ 2 + 2 * ((astar - b) ⬝ᵥ gv p x) ^ 2 := by
    intro x
    have heq : (u - astar) ⬝ᵥ gv p x = (u - b) ⬝ᵥ gv p x - (astar - b) ⬝ᵥ gv p x := by
      simp only [sub_dotProduct]; ring
    rw [heq]; nlinarith [sq_nonneg ((u - b) ⬝ᵥ gv p x + (astar - b) ⬝ᵥ gv p x)]
  have hint := integral_mono hi0 ((hi1.const_mul 2).add (hi2.const_mul 2)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul,
    integral_const_mul] at hint
  have hW1 : gW ℬ e (t + 1) S u ≤ gbeta d (t + 1) +
      ((u - astar) ⬝ᵥ S + NK ℬ astar S) ^ 2 / (gB d * ((t : ℝ) + 1)) := by
    unfold gW
    have h3 : gbeta d (t + 1) / 4 * sNorm ℬ (u - b) ^ 2 ≤ gbeta d (t + 1) := by
      have : sNorm ℬ (u - b) ^ 2 ≤ 4 := by
        have h0 : 0 ≤ sNorm ℬ (u - b) := by
          unfold sNorm; exact gauge_nonneg _
        nlinarith
      nlinarith
    have h4 : gZ ℬ e (t + 1) S u ^ 2 ≤ ((u - astar) ⬝ᵥ S + NK ℬ astar S) ^ 2 := by
      have : 0 ≤ gZ ℬ e (t + 1) S u := le_max_left _ _
      exact pow_le_pow_left₀ this hz1 2
    have h5 : gZ ℬ e (t + 1) S u ^ 2 / (gB d * ((t + 1 : ℕ) : ℝ)) ≤
        ((u - astar) ⬝ᵥ S + NK ℬ astar S) ^ 2 / (gB d * ((t : ℝ) + 1)) := by
      push_cast; exact div_le_div_of_nonneg_right h4 (by positivity)
    linarith
  have hW2 : gW ℬ e (t + 1) S astar ≤ gbeta d (t + 1) +
      NK ℬ astar S ^ 2 / (gB d * ((t : ℝ) + 1)) := by
    unfold gW
    have h3 : gbeta d (t + 1) / 4 * sNorm ℬ (astar - b) ^ 2 ≤ gbeta d (t + 1) := by
      have : sNorm ℬ (astar - b) ^ 2 ≤ 4 := by
        have h0 : 0 ≤ sNorm ℬ (astar - b) := by
          unfold sNorm; exact gauge_nonneg _
        nlinarith
      nlinarith
    have h4 : gZ ℬ e (t + 1) S astar ^ 2 ≤ NK ℬ astar S ^ 2 := by
      have : 0 ≤ gZ ℬ e (t + 1) S astar := le_max_left _ _
      exact pow_le_pow_left₀ this hz2 2
    have h5 : gZ ℬ e (t + 1) S astar ^ 2 / (gB d * ((t + 1 : ℕ) : ℝ)) ≤
        NK ℬ astar S ^ 2 / (gB d * ((t : ℝ) + 1)) := by
      push_cast; exact div_le_div_of_nonneg_right h4 (by positivity)
    linarith
  set X := (u - astar) ⬝ᵥ S
  set N := NK ℬ astar S
  have hsq : (X + N) ^ 2 + N ^ 2 ≤ (X + 2 * N) ^ 2 := by nlinarith
  have hfin : 2 * (gbeta d (t + 1) + (X + N) ^ 2 / (gB d * ((t : ℝ) + 1))) +
      2 * (gbeta d (t + 1) + N ^ 2 / (gB d * ((t : ℝ) + 1))) ≤
      4 * gbeta d (t + 1) + 2 * (X + 2 * N) ^ 2 / (gB d * ((t : ℝ) + 1)) := by
    have hden : 0 < gB d * ((t : ℝ) + 1) := by positivity
    have : 2 * ((X + N) ^ 2 + N ^ 2) / (gB d * ((t : ℝ) + 1)) ≤
        2 * (X + 2 * N) ^ 2 / (gB d * ((t : ℝ) + 1)) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    have e : 2 * (gbeta d (t + 1) + (X + N) ^ 2 / (gB d * ((t : ℝ) + 1))) +
        2 * (gbeta d (t + 1) + N ^ 2 / (gB d * ((t : ℝ) + 1))) =
        4 * gbeta d (t + 1) + 2 * ((X + N) ^ 2 + N ^ 2) / (gB d * ((t : ℝ) + 1)) := by ring
    linarith
  linarith

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_lt {n : ℕ} (hn : n < T) : Fx R T n = R.G n := if_pos hn

lemma hist_le_m (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t ≤ T) : R.hist t ≤ mΩ := by
  unfold GRun.hist
  refine iSup₂_le fun s hs => ?_
  obtain ⟨⟨hX, hA, hY, -⟩, -⟩ := hR s (by omega)
  exact (hX.prodMk (hA.prodMk hY)).comap_le

lemma Fx_le (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (_ : n ≤ T) : Fx R T n ≤ mΩ := by
  unfold Fx; split_ifs with h
  · exact G2R.G_le hR h
  · exact le_rfl

lemma cumEst_Fx (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n ≤ T) :
    Measurable[Fx R T n] (R.cumEst n) := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]; exact (G2R.meas_cumEst hR hn).mono (G2R.hist_le_G hR h) le_rfl
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact (G2R.meas_cumEst hR le_rfl).mono (hist_le_m hR le_rfl) le_rfl

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

lemma abs_dot_le_setNorm {𝒜 ℬ : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hgen : IsGenerator 𝒜 ℬ)
    (w : Fin d → ℝ) {x : Fin d → ℝ} (hx : x ∈ Kset ℬ) : |x ⬝ᵥ w| ≤ setNorm 𝒜 w := by
  rw [← G2R.conv_eq hgen] at hx
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} := by
    have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ w) :=
      ⟨fun x y => add_dotProduct x y w, fun c x => smul_dotProduct c x w⟩
    have : {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} =
        {v | v ⬝ᵥ w ≤ setNorm 𝒜 w} ∩ {v | -setNorm 𝒜 w ≤ v ⬝ᵥ w} := by
      ext x; simp [abs_le, and_comm]
    rw [this]
    exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
  exact convexHull_min (fun a ha => le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩) hcvx hx

lemma setNorm_eq {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (w : Fin d → ℝ) :
    setNorm 𝒜 w = max (supp 𝒜 w) (supp 𝒜 (-w)) := by
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨a, ha, rfl⟩
    show |a ⬝ᵥ w| ≤ _
    rcases le_total 0 (a ⬝ᵥ w) with h | h
    · rw [abs_of_nonneg h]; exact (le_supp h𝒜 ha w).trans (le_max_left _ _)
    · rw [abs_of_nonpos h]
      have := le_supp h𝒜 ha (-w)
      rw [dotProduct_neg] at this
      exact this.trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne w
      rw [← he]
      exact (le_abs_self _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)
    · obtain ⟨a, ha, he⟩ := supp_mem h𝒜 hne (-w)
      rw [← he, dotProduct_neg]
      exact (neg_le_abs _).trans (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)

lemma setNorm_cont {𝒜 : Set (Fin d → ℝ)} (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) :
    Continuous (setNorm 𝒜) := by
  have : setNorm 𝒜 = fun w => max (supp 𝒜 w) (supp 𝒜 (-w)) := funext (setNorm_eq h𝒜 hne)
  rw [this]
  exact (supp_cont h𝒜 hne).max ((supp_cont h𝒜 hne).comp continuous_neg)

lemma negMax_add_const {D : Set (Fin d → ℝ)} (V : Fin d → ℝ) (c k : ℝ) :
    negMax D V (c + k) = negMax D V c - k := by
  unfold negMax; ring

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma G_mono (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n < T) :
    R.G j ≤ R.G n := by
  induction n, hjn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hjn ih => exact (ih (by omega)).trans (hR n (by omega)).1.2.2.2.2.2.2.2.1

lemma Acum_Fx (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (θ : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) : Measurable[Fx R T n] (Acum 𝒜 R θ n) := by
  unfold Acum
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hθj : Measurable[R.G j] (R.θs j) := (hR j (by omega)).1.2.2.2.2.2.2.1
  have hc := (setNorm_cont h𝒜 hne).measurable
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt h]
    exact hc.comp ((hθj.mono (G_mono hR hj'.le h) le_rfl).sub measurable_const)
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]
    exact hc.comp (((hR j hj').1.2.2.2.1).sub measurable_const)

lemma setNorm_nonneg (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (w : Fin d → ℝ) : 0 ≤ setNorm 𝒜 w := by
  obtain ⟨a, ha⟩ := hne
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  exact le_trans (abs_nonneg (a ⬝ᵥ w)) (le_csSup (h𝒜.image hcont).bddAbove ⟨a, ha, rfl⟩)

lemma setNorm_sub_le (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) (x y : Fin d → ℝ) :
    setNorm 𝒜 (x - y) ≤ setNorm 𝒜 x + setNorm 𝒜 y := by
  have hc : ∀ w : Fin d → ℝ, Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := fun w => by
    simp only [dotProduct]; fun_prop
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨a, ha, rfl⟩
  show |a ⬝ᵥ (x - y)| ≤ _
  rw [dotProduct_sub]
  have h1 : |a ⬝ᵥ x| ≤ setNorm 𝒜 x := le_csSup (h𝒜.image (hc x)).bddAbove ⟨a, ha, rfl⟩
  have h2 : |a ⬝ᵥ y| ≤ setNorm 𝒜 y := le_csSup (h𝒜.image (hc y)).bddAbove ⟨a, ha, rfl⟩
  exact (abs_sub _ _).trans (add_le_add h1 h2)

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma negMaxW (astar θ : Fin d → ℝ) (C : ℝ) (n : ℕ) (ω : Ω) :
    negMax (Kset ℬ) (R.cumEst n ω) (cW 𝒜 R θ astar C n ω) =
      NK ℬ astar (R.cumEst n ω) + 2 * (C - Acum 𝒜 R θ n ω) := by
  unfold cW NK
  rw [show -(astar ⬝ᵥ R.cumEst n ω) - 2 * (C - Acum 𝒜 R θ n ω) =
    -(astar ⬝ᵥ R.cumEst n ω) + -(2 * (C - Acum 𝒜 R θ n ω)) by ring, negMax_add_const]
  ring

lemma Acum_le (h𝒜 : IsCompact 𝒜) (hne : 𝒜.Nonempty) {θ : Fin d → ℝ} {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) :
    ∀ᵐ ω ∂P, ∀ n ≤ T, 0 ≤ Acum 𝒜 R θ n ω ∧ Acum 𝒜 R θ n ω ≤ C := by
  filter_upwards [hcor.2] with ω hω n hn
  refine ⟨Finset.sum_nonneg fun j _ => setNorm_nonneg h𝒜 hne _, le_trans ?_ hω⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
    (fun j _ _ => setNorm_nonneg h𝒜 hne _)

end G26R


-- ===== Solutions.G26.Geo =====

/-! ### The projective body of normalized directions (Lemma G.16) -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G26G

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma ne𝒜 : 𝒜.Nonempty := ⟨astar, H.hastar⟩

lemma haK : astar ∈ Kset ℬ := H.hgen.2 H.hastar

lemma Kc : IsCompact (Kset ℬ) := G2R.Kset_compact H.hℬ

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RunN =====

/-! ### The normalized field on the cone body satisfies the field interface (Lemmas G.17, G.28) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_mono' (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {j n : ℕ} (hjn : j ≤ n) (hn : n ≤ T) :
    Fx R T j ≤ Fx R T n := by
  rcases lt_or_eq_of_le hn with h | h
  · rw [Fx_lt (lt_of_le_of_lt hjn h), Fx_lt h]; exact G_mono hR hjn h
  · subst h
    have : Fx R n n = mΩ := if_neg (lt_irrefl n)
    rw [this]; exact Fx_le hR (le_trans hjn le_rfl)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma gbeta_ge16 (n : ℕ) : 16 ≤ gbeta d (n + 1) := by
  unfold gbeta; have : (1 : ℝ) ≤ d := by exact_mod_cast H.hd
  have := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ); linarith

lemma kappa_facts (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) (ω : Ω) :
    0 ≤ setNorm 𝒜 (R.θs n ω - θ) ∧ setNorm 𝒜 (R.θs n ω - θ) ≤ 2 := by
  have hne𝒜 := H.ne𝒜
  have hθn := (hR n hn).2.2.2.2.2
  refine ⟨setNorm_nonneg H.h𝒜 hne𝒜 _, ?_⟩
  have := setNorm_sub_le H.h𝒜 hne𝒜 (R.θs n ω) θ
  linarith [hθn ω, H.hθ]

end Sharp

end G26G


-- ===== Solutions.G26.RunSI =====

/-! ### Compensated per-action scalar processes (Lemma G.29, (G.635)–(G.641)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Ecor_succ (θ w : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    Ecor R θ w (n + 1) ω = Ecor R θ w n ω + w ⬝ᵥ (R.θs n ω - θ) := by
  unfold Ecor; rw [Finset.sum_range_succ]

lemma YF_succ (θ astar : Fin d → ℝ) (C : ℝ) (τ : ℕ → ℝ) (a : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YF R θ astar C τ a (n + 1) ω - YF R θ astar C τ a n ω =
      (a - astar) ⬝ᵥ R.thetaHat n ω - (a - astar) ⬝ᵥ (R.θs n ω - θ) + 2 * (τ (n + 1) - τ n) := by
  simp only [YF, cumEst_succ, Ecor_succ, dotProduct_add]; ring

lemma Ecor_Fx (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (θ w : Fin d → ℝ) {n : ℕ} (hn : n ≤ T) :
    Measurable[Fx R T n] (Ecor R θ w n) := by
  unfold Ecor
  refine Finset.measurable_sum _ fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have hθj : Measurable[R.G j] (R.θs j) := (hR j (by omega)).1.2.2.2.2.2.2.1
  have hle : R.G j ≤ Fx R T n := by
    have := Fx_mono' hR (le_of_lt hj') hn
    rwa [Fx_lt (by omega : j < T)] at this
  exact G2R.meas_dot' measurable_const ((hθj.mono hle le_rfl).sub measurable_const)

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma abs_dot_two {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (w : Fin d → ℝ) :
    |(a - astar) ⬝ᵥ w| ≤ 2 * setNorm 𝒜 w := by
  rw [sub_dotProduct]
  have h1 := abs_dot_le_setNorm H.h𝒜 H.hgen w ha
  have h2 := abs_dot_le_setNorm H.h𝒜 H.hgen w H.haK
  linarith [abs_sub (a ⬝ᵥ w) (astar ⬝ᵥ w)]

lemma Ecor_le {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (n : ℕ) (ω : Ω) :
    |Ecor R θ (a - astar) n ω| ≤ 2 * Acum 𝒜 R θ n ω := by
  unfold Ecor Acum
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => H.abs_dot_two ha _)

lemma YF_low {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) {C : ℝ} {τ : ℕ → ℝ} {n : ℕ} {ω : Ω}
    (hA0 : 0 ≤ Acum 𝒜 R θ n ω) (hAC : Acum 𝒜 R θ n ω ≤ C)
    (hQ : negMax (Kset ℬ) (R.cumEst n ω) (cW 𝒜 R θ astar C n ω) ≤ τ n) :
    τ n ≤ YF R θ astar C τ a n ω ∧
      (a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω) ≤ YF R θ astar C τ a n ω ∧
      0 ≤ (a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω) := by
  rw [negMaxW] at hQ
  obtain ⟨hN0, hNu⟩ := NK_facts H.hd H.hℬ H.hgen H.hspan H.haK (R.cumEst n ω) ha
  have hE := H.Ecor_le (R := R) ha n ω
  unfold YF
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.1 hE).2]
  · linarith [(abs_le.1 hE).2]
  · linarith

/-- **the compensated per-action variable is a scalar interface (G.636)–(G.641)** -/
theorem runF_SI (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} (hcor : IsCorruptedG P 𝒜 θ C T R)
    {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) {τ : ℕ → ℝ} (hτpos : ∀ n, 0 < τ n)
    (hτmono : ∀ n, τ n ≤ τ (n + 1)) (hδ : ∀ n, τ (n + 1) - τ n ≤ 1) {m0 N : ℕ} (hN : N ≤ T)
    (hτB : ∀ n, m0 ≤ n → gB d * (gbeta d (n + 1) + 3) ≤ τ n) :
    SI P (Fx R T) (YF R θ astar C τ a) (IW 𝒜 ℬ R θ astar C τ m0) m0 N τ
      (fun n => gbeta d (n + 1)) (gB d) where
  Fle := fun n hn => Fx_le hR (hn.trans hN)
  Ym := fun n hn => by
    have h1 := G2R.meas_dot' (measurable_const (a := a - astar)) (cumEst_Fx hR (hn.trans hN))
    exact ((h1.sub (Ecor_Fx hR θ (a - astar) (hn.trans hN))).add measurable_const).add
      measurable_const
  Im := fun n hn => by
    have hT := hn.trans hN
    have : IW 𝒜 ℬ R θ astar C τ m0 n = ⋂ j : ℕ, {ω | m0 ≤ j → j ≤ n →
        negMax (Kset ℬ) (R.cumEst j ω) (cW 𝒜 R θ astar C j ω) ≤ τ j} := by
      ext ω; simp [IW]
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    by_cases h : m0 ≤ j ∧ j ≤ n
    · have e1 : {ω | m0 ≤ j → j ≤ n → negMax (Kset ℬ) (R.cumEst j ω) (cW 𝒜 R θ astar C j ω) ≤ τ j} =
          {ω | negMax (Kset ℬ) (R.cumEst j ω) (cW 𝒜 R θ astar C j ω) ≤ τ j} := by
        ext ω; simp [h.1, h.2]
      rw [e1]
      have hS := cumEst_Fx hR (le_trans h.2 hT)
      have hc : Measurable[Fx R T j] (cW 𝒜 R θ astar C j) :=
        (G2R.meas_dot' measurable_const hS).neg.sub
          (measurable_const.mul (measurable_const.sub (Acum_Fx H.h𝒜 H.ne𝒜 hR θ (le_trans h.2 hT))))
      have hm := G26.negMax_meas H.Kc ⟨astar, H.haK⟩ hS hc
      exact Fx_mono' hR h.2 hT _ (measurableSet_le hm measurable_const)
    · have e1 : {ω | m0 ≤ j → j ≤ n → negMax (Kset ℬ) (R.cumEst j ω) (cW 𝒜 R θ astar C j ω) ≤ τ j} =
          univ := by
        ext ω; simp only [mem_setOf_eq, mem_univ, iff_true]
        intro h1 h2; exact absurd ⟨h1, h2⟩ h
      rw [e1]; exact MeasurableSet.univ
  Imono := fun n ω hω j hj1 hj2 => hω j hj1 (by omega)
  τpos := hτpos
  low := by
    intro n hmn hnN
    filter_upwards [Acum_le H.h𝒜 H.ne𝒜 hcor] with ω hA hI
    obtain ⟨hA0, hAC⟩ := hA n (hnN.trans hN)
    exact (H.YF_low ha hA0 hAC (hI n hmn le_rfl)).1
  env := by
    intro n hn
    refine ⟨G2R.rho d n + 4 * n + 2 * |C| + 2 * |τ n|, ?_⟩
    filter_upwards [G2R.range_bound H.hd H.hℬ H.hgen H.hspan hR n (hn.trans hN)] with ω h
    have h1 := h a ha astar H.haK
    have h2 : |Ecor R θ (a - astar) n ω| ≤ 4 * n := by
      unfold Ecor
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ j ∈ Finset.range n, |(a - astar) ⬝ᵥ (R.θs j ω - θ)| ≤ 4 := by
        intro j hj
        have hj' := Finset.mem_range.1 hj
        refine (H.abs_dot_two ha _).trans ?_
        obtain ⟨-, h2⟩ := H.kappa_facts hR (by omega : j < T) ω
        linarith
      refine (Finset.sum_le_sum this).trans ?_
      simp; linarith
    unfold YF
    calc |(a - astar) ⬝ᵥ R.cumEst n ω - Ecor R θ (a - astar) n ω + 2 * C + 2 * τ n|
        ≤ |(a - astar) ⬝ᵥ R.cumEst n ω| + |Ecor R θ (a - astar) n ω| + |2 * C| + |2 * τ n| := by
          have := abs_add_le ((a - astar) ⬝ᵥ R.cumEst n ω - Ecor R θ (a - astar) n ω + 2 * C)
            (2 * τ n)
          have := abs_add_le ((a - astar) ⬝ᵥ R.cumEst n ω - Ecor R θ (a - astar) n ω) (2 * C)
          have := abs_sub ((a - astar) ⬝ᵥ R.cumEst n ω) (Ecor R θ (a - astar) n ω)
          linarith
      _ ≤ _ := by
          rw [abs_mul, abs_mul, abs_two]; linarith
  mag := by
    intro n hmn hnN
    have hnT : n < T := lt_of_lt_of_le hnN hN
    filter_upwards [G2R.X_mem_K hR H.hℬ hnT, Acum_le H.h𝒜 H.ne𝒜 hcor] with ω hX hA hI
    obtain ⟨hA0, hAC⟩ := hA n hnT.le
    obtain ⟨hlow, hXN, hXN0⟩ := H.YF_low ha hA0 hAC (hI n hmn le_rfl)
    rw [YF_succ]
    have hY := (hR n hnT).2.2.2.2.1.1 ω
    have hm := magK (e := e) H.hd H.hℬ H.hgen H.hspan H.haK (G2R.feas hR hnT ω) hX ha
    have hB := G2R.gB_pos (d := d)
    have h1 : |(a - astar) ⬝ᵥ R.thetaHat n ω| ≤ 2 * gbeta d (n + 1) +
        YF R θ astar C τ a n ω / gB d := by
      rw [GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      refine (mul_le_of_le_one_left (abs_nonneg _) hY).trans (hm.trans ?_)
      have := div_le_div_of_nonneg_right hXN hB.le
      linarith
    have h2 : |(a - astar) ⬝ᵥ (R.θs n ω - θ)| ≤ 4 := by
      refine (H.abs_dot_two ha _).trans ?_
      obtain ⟨-, h2⟩ := H.kappa_facts hR hnT ω
      linarith
    have h3 : |2 * (τ (n + 1) - τ n)| ≤ 2 := by
      rw [abs_mul, abs_two, abs_of_nonneg (by linarith [hτmono n])]; linarith [hδ n]
    have h4 : gB d * (gbeta d (n + 1) + 3) ≤ YF R θ astar C τ a n ω := (hτB n hmn).trans hlow
    have h5 : 2 * gbeta d (n + 1) + 6 ≤ 2 * YF R θ astar C τ a n ω / gB d := by
      rw [le_div_iff₀ hB]; nlinarith
    calc |(a - astar) ⬝ᵥ R.thetaHat n ω - (a - astar) ⬝ᵥ (R.θs n ω - θ) + 2 * (τ (n + 1) - τ n)|
        ≤ |(a - astar) ⬝ᵥ R.thetaHat n ω| + |(a - astar) ⬝ᵥ (R.θs n ω - θ)| +
            |2 * (τ (n + 1) - τ n)| := by
          have := abs_add_le ((a - astar) ⬝ᵥ R.thetaHat n ω - (a - astar) ⬝ᵥ (R.θs n ω - θ))
            (2 * (τ (n + 1) - τ n))
          have := abs_sub ((a - astar) ⬝ᵥ R.thetaHat n ω) ((a - astar) ⬝ᵥ (R.θs n ω - θ))
          linarith
      _ ≤ 3 * YF R θ astar C τ a n ω / gB d := by
          have : 3 * YF R θ astar C τ a n ω / gB d = YF R θ astar C τ a n ω / gB d +
            2 * YF R θ astar C τ a n ω / gB d := by ring
          linarith
  sec := by
    intro n hmn hnN
    have hnT : n < T := lt_of_lt_of_le hnN hN
    have hGle := G2R.G_le hR hnT
    have hKc := H.Kc
    have hSm : Measurable[R.G n] (R.cumEst n) :=
      (G2R.meas_cumEst hR hnT.le).mono (G2R.hist_le_G hR hnT) le_rfl
    set h : Ω → ℝ := fun ω => 4 * gbeta d (n + 1) +
      2 * ((a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω)) ^ 2 /
        (gB d * ((n : ℝ) + 1)) with hh
    have hNm : Measurable[R.G n] (fun ω => NK ℬ astar (R.cumEst n ω)) :=
      G26.negMax_meas hKc ⟨astar, H.haK⟩ hSm (G2R.meas_dot' measurable_const hSm).neg
    have hXm : Measurable[R.G n] (fun ω => (a - astar) ⬝ᵥ R.cumEst n ω) :=
      G2R.meas_dot' (measurable_const (a := a - astar)) hSm
    have hhm : StronglyMeasurable[R.G n] h :=
      (measurable_const.add ((((hXm.add (hNm.const_mul 2)).pow_const 2).const_mul 2).div_const
        _)).stronglyMeasurable
    have hhi : Integrable h P := by
      refine Integrable.of_bound (hhm.mono hGle).aestronglyMeasurable
        (4 * gbeta d (n + 1) + 2 * (3 * G2R.rho d n) ^ 2 / (gB d * ((n : ℝ) + 1))) ?_
      filter_upwards [G2R.range_bound H.hd H.hℬ H.hgen H.hspan hR n hnT.le] with ω hω
      have hβ := G2R.gbeta_pos H.hd (n + 1)
      have hB := G2R.gB_pos (d := d)
      obtain ⟨hN0, hNu⟩ := NK_facts H.hd H.hℬ H.hgen H.hspan H.haK (R.cumEst n ω) ha
      have hX := hω a ha astar H.haK
      have hNr : NK ℬ astar (R.cumEst n ω) ≤ G2R.rho d n := by
        unfold NK
        obtain ⟨x0, hx0, hx0e⟩ := negMax_mem hKc ⟨astar, H.haK⟩ (R.cumEst n ω)
          (-(astar ⬝ᵥ R.cumEst n ω))
        rw [← hx0e, fzK]
        have := hω x0 hx0 astar H.haK
        linarith [neg_abs_le ((x0 - astar) ⬝ᵥ R.cumEst n ω)]
      have h1 : ((a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω)) ^ 2 ≤
          (3 * G2R.rho d n) ^ 2 := by
        have h2 : 0 ≤ (a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω) := by linarith
        exact pow_le_pow_left₀ h2 (by linarith [le_abs_self ((a - astar) ⬝ᵥ R.cumEst n ω)]) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [hh]; positivity)]
      simp only [hh]
      gcongr
    have hcw : ∀ᵐ ω ∂P, |(a - astar) ⬝ᵥ gv (R.p n ω) (R.X n ω)| ≤
        2 * (gbeta d (n + 1) + G2R.rho d n / gB d) := by
      filter_upwards [G2R.v_bound_ae H.hd H.hℬ H.hgen H.hspan hR hnT] with ω h
      exact h.2 a ha astar H.haK
    have hcs := cond_sec H.hd H.hℬ hR hnT (a - astar) hcw hhm hhi
      (ae_of_all _ fun ω => secK (e := e) H.hd H.hℬ H.hgen H.hspan H.haK (G2R.feas hR hnT ω) ha)
    have hθn := (hR n hnT).2.2.2.2.2
    have hcm := cond_mean H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT (a - astar) hcw (cθ := 2)
      (fun ω => by
        rw [sub_dotProduct]
        have h1 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) ha
        have h2 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) H.haK
        exact (abs_sub _ _).trans (by linarith))
    set g : Ω → ℝ := fun ω => -((a - astar) ⬝ᵥ (R.θs n ω - θ)) + 2 * (τ (n + 1) - τ n) with hg
    have hgm : StronglyMeasurable[R.G n] g :=
      (((G2R.meas_dot' measurable_const (((hR n hnT).1.2.2.2.2.2.2.1).sub measurable_const)).neg).add
        measurable_const).stronglyMeasurable
    have hgb : ∀ ω, |g ω| ≤ 6 := fun ω => by
      have h1 : |(a - astar) ⬝ᵥ (R.θs n ω - θ)| ≤ 4 := by
        refine (H.abs_dot_two ha _).trans ?_
        obtain ⟨-, h2⟩ := H.kappa_facts hR hnT ω
        linarith
      have h2 : |2 * (τ (n + 1) - τ n)| ≤ 2 := by
        rw [abs_mul, abs_two, abs_of_nonneg (by linarith [hτmono n])]; linarith [hδ n]
      simp only [hg]
      have := abs_add_le (-((a - astar) ⬝ᵥ (R.θs n ω - θ))) (2 * (τ (n + 1) - τ n))
      rw [abs_neg] at this
      linarith
    have hfi : Integrable (fun ω => (a - astar) ⬝ᵥ R.thetaHat n ω) P := by
      have := (unbiased_φ H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT (a - astar) hcw (φ := fun _ => 1)
        measurable_const (fun _ => by simp)).1
      simpa using this
    have hf2 : Integrable (fun ω => ((a - astar) ⬝ᵥ R.thetaHat n ω) ^ 2) P := by
      refine Integrable.of_bound (hfi.aestronglyMeasurable.pow 2)
        ((2 * (gbeta d (n + 1) + G2R.rho d n / gB d)) ^ 2) ?_
      filter_upwards [hcw] with ω h
      rw [Real.norm_eq_abs, abs_pow, GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
      have hY := (hR n hnT).2.2.2.2.1.1 ω
      exact pow_le_pow_left₀ (by positivity) ((mul_le_of_le_one_left (abs_nonneg _) hY).trans h) 2
    have hsh := (condExp_shift (G := R.G) hGle hfi hf2 hgm hgb).2
    have e1 : (fun ω => (YF R θ astar C τ a (n + 1) ω - YF R θ astar C τ a n ω) ^ 2) =
        fun ω => ((a - astar) ⬝ᵥ R.thetaHat n ω + g ω) ^ 2 :=
      funext fun ω => by rw [YF_succ]; simp only [hg]; ring
    rw [e1, Fx_lt hnT]
    filter_upwards [hsh, hcs, hcm, Acum_le H.h𝒜 H.ne𝒜 hcor] with ω h1 h2 h3 hA hI
    rw [h1, h3]
    obtain ⟨hA0, hAC⟩ := hA n hnT.le
    obtain ⟨hlow, hXN, hXN0⟩ := H.YF_low ha hA0 hAC (hI n hmn le_rfl)
    have hβ := H.gbeta_ge16 n
    have hB := G2R.gB_pos (d := d)
    have hd2 : |(a - astar) ⬝ᵥ R.θs n ω| ≤ 2 := by
      rw [sub_dotProduct]
      have h1 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) ha
      have h2 := G2R.abs_dot_le_one H.h𝒜 H.hgen (hθn ω) H.haK
      exact (abs_sub _ _).trans (by linarith)
    have hg6 := hgb ω
    have h4 : ((a - astar) ⬝ᵥ R.cumEst n ω + 2 * NK ℬ astar (R.cumEst n ω)) ^ 2 ≤
        YF R θ astar C τ a n ω ^ 2 := pow_le_pow_left₀ hXN0 hXN 2
    have h5 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : (0 : ℝ) ≤ gB d * ((n : ℝ) + 1))
    have h6 : 2 * g ω * ((a - astar) ⬝ᵥ R.θs n ω) ≤ 24 := by
      have := abs_mul (g ω) ((a - astar) ⬝ᵥ R.θs n ω)
      have h7 : |g ω * ((a - astar) ⬝ᵥ R.θs n ω)| ≤ 6 * 2 :=
        by rw [abs_mul]; exact mul_le_mul hg6 hd2 (abs_nonneg _) (by norm_num)
      linarith [le_abs_self (g ω * ((a - astar) ⬝ᵥ R.θs n ω))]
    have h7 : g ω ^ 2 ≤ 36 := by
      have : |g ω| ^ 2 ≤ 6 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hg6 2
      rw [sq_abs] at this; linarith
    simp only [hh] at h2
    linarith

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.runF_SI := @G26G.Sharp.runF_SI
