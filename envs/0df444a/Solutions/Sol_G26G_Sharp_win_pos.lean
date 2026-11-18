-- Prove2me | solution 1 for G26G.Sharp.win_pos
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:36:35.453685+00:00
-- url     : https://prove2.me/submissions/281f9e9c-8a6b-4a4c-ab40-628165644547

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_G26_FI_absMax_env
import Theorems.Thm_G26_SI_pos_moment
import Theorems.Thm_G26G_Sharp_runN_SI
import Theorems.Thm_G26R_runK_FI
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

lemma Sset_sub_ball {𝒜 : Set (Fin d → ℝ)} (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) :
    IAFTRL.Sset 𝒜 ⊆ Metric.closedBall 0 1 := by
  refine convexHull_min ?_ (convex_closedBall 0 1)
  have h1 : ∀ a ∈ 𝒜, ‖a‖ ≤ 1 := by
    intro a ha
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have : a i * a i ≤ a ⬝ᵥ a :=
      Finset.single_le_sum (f := fun j => a j * a j) (fun j _ => mul_self_nonneg _)
        (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    have := hball a ha
    nlinarith [abs_mul_abs_self (a i), abs_nonneg (a i)]
  rintro x (hx | hx)
  · simpa using h1 x hx
  · have := h1 (-x) (by simpa using hx)
    simpa [norm_neg] using this

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

lemma norm_le_sNorm {𝒜 : Set (Fin d → ℝ)} (hne : 𝒜.Nonempty) (hspan : Submodule.span ℝ 𝒜 = ⊤)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (x : Fin d → ℝ) : ‖x‖ ≤ IAFTRL.sNorm 𝒜 x := by
  have := le_gauge_of_subset_closedBall (absorbent_nhds_zero (Sset_nhds hne hspan)) zero_le_one
    (Sset_sub_ball hball) (x := x)
  simpa [IAFTRL.sNorm] using this

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


-- ===== Solutions.G1.Geo2 =====

/-! ### Generator geometry helpers -/

open MeasureTheory ProbabilityTheory Set IAFTRL

namespace G1L

variable {d : ℕ}

lemma Sset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Sset 𝒜 = Sset ℬ := by
  unfold Sset
  apply le_antisymm
  · refine convexHull_min ?_ (convex_convexHull ℝ _)
    rintro x (hx | hx)
    · exact convexHull_mono subset_union_left (hgen.2 hx)
    · have h1 : -x ∈ convexHull ℝ ℬ := hgen.2 hx
      have h2 : x ∈ convexHull ℝ (-ℬ) := by
        rw [convexHull_neg, Set.mem_neg]; exact h1
      exact convexHull_mono subset_union_right h2
  · exact convexHull_mono (union_subset_union hgen.1 (Set.neg_subset_neg.2 hgen.1))

lemma sNorm_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) (x : Fin d → ℝ) :
    sNorm 𝒜 x = sNorm ℬ x := by
  unfold sNorm; rw [Sset_gen hgen]

lemma Kset_gen {𝒜 ℬ : Set (Fin d → ℝ)} (hgen : IsGenerator 𝒜 ℬ) : Kset 𝒜 = Kset ℬ :=
  ((convexHull_mono hgen.1).antisymm (convexHull_min hgen.2 (convex_convexHull ℝ ℬ))).symm

end G1L


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

lemma feas (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsFeasible3_6 ℬ e (t + 1) (R.cumEst t ω) (R.p t ω) :=
  ((hR t ht).2.1.2 ω).1

lemma p_prob (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    IsProbabilityMeasure (R.p t ω) :=
  (feas hR ht ω).1

lemma p_supp (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {t : ℕ} (ht : t < T) (ω : Ω) :
    R.p t ω (Kset ℬ)ᶜ = 0 :=
  (feas hR ht ω).2.1

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

lemma posMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    u ⬝ᵥ V + c ≤ posMax D V c := by
  have := le_supp hD hu V
  unfold posMax; linarith

lemma abs_le_absMax {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    |u ⬝ᵥ V + c| ≤ absMax D V c := by
  unfold absMax
  refine abs_le.2 ⟨?_, le_trans (posMax_ge hD hu V c) (le_max_left _ _)⟩
  have := le_trans (negMax_ge hD hu V c) (le_max_right (posMax D V c) _)
  linarith

omit hD in
lemma negMax_le_absMax (V : Fin d → ℝ) (c : ℝ) : negMax D V c ≤ absMax D V c :=
  le_max_right _ _

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma posMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, u ⬝ᵥ V + c = posMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne V
  exact ⟨u, hu, by unfold posMax; linarith⟩

/-- the absolute maximum is attained -/
lemma absMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, |u ⬝ᵥ V + c| = absMax D V c ∧ ∀ x ∈ D, |x ⬝ᵥ V + c| ≤ |u ⬝ᵥ V + c| := by
  obtain ⟨u1, hu1, h1⟩ := posMax_mem hD hne V c
  obtain ⟨u2, hu2, h2⟩ := negMax_mem hD hne V c
  rcases le_total (negMax D V c) (posMax D V c) with h | h
  · have hA : absMax D V c = posMax D V c := max_eq_left h
    have hval : |u1 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, h1]
      refine abs_of_nonneg ?_
      have := negMax_ge hD hu1 V c
      linarith
    exact ⟨u1, hu1, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩
  · have hA : absMax D V c = negMax D V c := max_eq_right h
    have hval : |u2 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, ← h2, abs_of_nonpos]
      have := posMax_ge hD hu2 V c
      linarith
    exact ⟨u2, hu2, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma posMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => posMax D p.1 p.2 := by
  unfold posMax
  exact ((supp_cont hD hne).comp continuous_fst).add continuous_snd

lemma absMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => absMax D p.1 p.2 :=
  (posMax_cont hD hne).max (negMax_cont hD hne)

lemma absMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => absMax D (V ω) (c ω) := by
  have h := (absMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- the field at a fixed point is `F_n`-measurable -/
lemma FI.fz_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (u : Fin d → ℝ) :
    Measurable[F n] (fun ω => fz V c n ω u) := by
  unfold fz
  have h : Continuous fun p : (Fin d → ℝ) × ℝ => u ⬝ᵥ p.1 + p.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp ((I.Vm n hn).prodMk (I.cm n hn))

lemma FI.absMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => absMax D (V n ω) (c n ω)) :=
  G26.absMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

/-- deterministic envelope of the field and its extrema -/
lemma FI.env' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᵐ ω ∂μ, absMax D (V n ω) (c n ω) ≤ r ∧
      ∀ u ∈ D, |fz V c n ω u| ≤ r := by
  obtain ⟨r, hr⟩ := I.env n hn
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  filter_upwards [hr] with ω h
  obtain ⟨x0, hx0, hval, -⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : absMax D (V n ω) (c n ω) ≤ max r 0 := by
    rw [← hval]; exact (h x0 hx0).trans (le_max_left _ _)
  exact ⟨hA, fun u hu => (abs_le_absMax I.hD hu _ _).trans hA⟩

end

end G26


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma survS_anti (A : ℕ → Set Ω) {m n : ℕ} (h : m ≤ n) : survS A n ⊆ survS A m := by
  intro ω hω
  simp only [survS, Set.mem_iInter, Finset.mem_range] at hω ⊢
  exact fun i hi => hω i (by omega)

/-- on the surviving set the frozen field is the field -/
lemma frz_eq {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) :
    ∀ n ω, (n = 0 ∨ ω ∈ survS A (n - 1)) → frz X A n ω = X n ω := by
  intro n ω h
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_sub_cancel] at h
    rcases h with h | h
    · omega
    · simp only [frz, if_pos h]

lemma frz_eq_of_mem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∈ survS A n) : frz X A n ω = X n ω := by
  cases n with
  | zero => rfl
  | succ n => exact frz_eq X A (n + 1) ω (Or.inr (survS_anti A (by omega) h))

lemma frz_succ_of_notMem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∉ survS A n) : frz X A (n + 1) ω = frz X A n ω := by
  simp only [frz, if_neg h]

/-- once frozen at the first failure `i`, the field stays at its value at `i` -/
lemma frz_stop {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {i : ℕ} {ω : Ω}
    (hi : i = 0 ∨ ω ∈ survS A (i - 1)) (hfail : ω ∉ A i) :
    ∀ N, i ≤ N → frz X A N ω = X i ω := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact frz_eq X A i ω hi
  | succ N hiN ih =>
    have hnot : ω ∉ survS A N := by
      intro h
      have := survS_anti A hiN h
      simp only [survS, Set.mem_iInter, Finset.mem_range] at this
      exact hfail (this i (by omega))
    rw [frz_succ_of_notMem X A hnot, ih]

/-- the frozen pair `(V, c)` at time `n` equals the pair at a common earlier time -/
lemma frz_pair_exists (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) :
    ∀ n ω, ∃ i ≤ n, frz V A n ω = V i ω ∧ frz c A n ω = c i ω := by
  intro n ω
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, rfl⟩
  | succ n ih =>
    by_cases h : ω ∈ survS A n
    · exact ⟨n + 1, le_rfl, by simp only [frz, if_pos h], by simp only [frz, if_pos h]⟩
    · obtain ⟨i, hi, he, he'⟩ := ih
      exact ⟨i, by omega, by rw [frz_succ_of_notMem V A h, he],
        by rw [frz_succ_of_notMem c A h, he']⟩

/-- the increment of the frozen field -/
lemma fxi_frz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    fxi (frz V A) (frz c A) n ω u = (survS A n).indicator (fun ω => fxi V c n ω u) ω := by
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h]
    unfold fxi fz
    rw [frz_eq_of_mem V A h, frz_eq_of_mem c A h]
    simp only [frz, if_pos h]
  · rw [Set.indicator_of_notMem h]
    unfold fxi fz
    rw [frz_succ_of_notMem V A h, frz_succ_of_notMem c A h]; ring

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.Fmono' (I : FI D μ F T V c J β B lo hi m0) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ T) :
    F m ≤ F n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (ih (by omega)).trans (I.Fmono n (by omega))

lemma FI.survS_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[F n] (survS A n) := by
  unfold survS
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact I.Fmono' (by omega) hn _ (hA i (by omega))

lemma FI.frz_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (hX : ∀ n ≤ T, Measurable[F n] (X n)) :
    ∀ n ≤ T, Measurable[F n] (frz X A n) := by
  intro n hn
  induction n with
  | zero => exact hX 0 hn
  | succ n ih =>
    have hS := I.survS_meas hA (n := n) (by omega)
    have hmono := I.Fmono n (by omega)
    classical
    show Measurable[F (n + 1)] fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω
    exact Measurable.ite (hmono _ hS) (hX (n + 1) hn) ((ih (by omega)).mono hmono le_rfl)

lemma FI.fxi_int [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n < T)
    {u : Fin d → ℝ} (hu : u ∈ D) :
    ∃ r : ℝ, Integrable (fun ω => fxi V c n ω u) μ ∧ ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r := by
  obtain ⟨r0, -, hr0⟩ := I.env' hn.le
  obtain ⟨r1, -, hr1⟩ := I.env' (n := n + 1) hn
  have hb : ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r1 + r0 := by
    filter_upwards [hr0, hr1] with ω h0 h1
    unfold fxi
    exact le_trans (abs_sub _ _) (add_le_add (h1.2 u hu) (h0.2 u hu))
  refine ⟨r1 + r0, ?_, hb⟩
  have hm : Measurable (fun ω => fxi V c n ω u) := by
    unfold fxi
    exact ((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((I.fz_meas hn.le u).mono (I.Fle n hn.le) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable _ (by
    filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])

lemma FI.frz_N0 (I : FI D μ F T V c J β B lo hi m0) (A : ℕ → Set Ω) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂μ, 0 ≤ negMax D (frz V A n ω) (frz c A n ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), 0 ≤ negMax D (V i ω) (c i ω) :=
    ae_all_iff.2 fun i => I.N0 i (by have := i.2; omega)
  filter_upwards [hall] with ω hω
  obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
  rw [hV, hc]; exact hω ⟨i, by omega⟩

/-- **freezing preserves the field interface** -/
theorem FI.freeze [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) {J' : ℕ → Set Ω} (hJ'm : ∀ n ≤ T, MeasurableSet[F n] (J' n))
    (hJ'mono : ∀ n, J' (n + 1) ⊆ J' n) (hAJ : ∀ n, survS A n ∩ J' n ⊆ J n) :
    FI D μ F T (frz V A) (frz c A) J' β B lo hi m0 where
  hD := I.hD
  hconv := I.hconv
  hne := I.hne
  Fle := I.Fle
  Fmono := I.Fmono
  Vm := I.frz_meas hA V I.Vm
  cm := I.frz_meas hA c I.cm
  Jm := hJ'm
  Jmono := hJ'mono
  env := by
    intro n hn
    have : ∀ i ∈ Finset.range (n + 1), ∃ r : ℝ, ∀ᵐ ω ∂μ, ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r :=
      fun i hi => I.env i (by have := Finset.mem_range.1 hi; omega)
    choose r hr using this
    refine ⟨∑ i ∈ (Finset.range (n + 1)).attach, max (r i.1 i.2) 0, ?_⟩
    have hall : ∀ᵐ ω ∂μ, ∀ i : Finset.range (n + 1), ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r i.1 i.2 :=
      ae_all_iff.2 fun i => hr i.1 i.2
    filter_upwards [hall] with ω hω u hu
    obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle : max (r i hmem) 0 ≤ ∑ j ∈ (Finset.range (n + 1)).attach, max (r j.1 j.2) 0 :=
      Finset.single_le_sum (f := fun j : Finset.range (n + 1) => max (r j.1 j.2) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_attach _ ⟨i, hmem⟩)
    rw [hV, hc]
    exact ((hω ⟨i, hmem⟩ u hu).trans (le_max_left _ _)).trans hle
  N0 := fun n hn => I.frz_N0 A hn
  drift := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, -⟩ := I.fxi_int hn hu
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u) =
          (survS A n).indicator (fun ω => fxi V c n ω u) := by
        funext ω; exact fxi_frz V c A n ω u
      rw [e]
      exact condExp_indicator hint hS
    filter_upwards [hce, I.drift n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω]; exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]; exact ⟨hlo, hhi⟩
  mag := by
    intro n hm0 hn
    filter_upwards [I.mag n hm0 hn, I.frz_N0 A hn.le] with ω hω hN hJ u hu
    by_cases hS : ω ∈ survS A n
    · rw [fxi_frz, Set.indicator_of_mem hS, fz, frz_eq_of_mem V A hS, frz_eq_of_mem c A hS]
      exact hω (hAJ n ⟨hS, hJ⟩) u hu
    · rw [fxi_frz, Set.indicator_of_notMem hS, abs_zero]
      have h1 := negMax_ge I.hD hu (frz V A n ω) (frz c A n ω)
      have h2 : 0 ≤ fz (frz V A) (frz c A) n ω u + 2 * negMax D (frz V A n ω) (frz c A n ω) := by
        unfold fz; linarith
      have := hβ n
      positivity
  sec := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, hb⟩ := I.fxi_int hn hu
    have hint2 : Integrable (fun ω => fxi V c n ω u ^ 2) μ := by
      refine Integrable.of_bound (hint.aestronglyMeasurable.pow 2) (r ^ 2) ?_
      filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u ^ 2 | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u ^ 2 | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u ^ 2) =
          (survS A n).indicator (fun ω => fxi V c n ω u ^ 2) := by
        funext ω
        rw [fxi_frz]
        by_cases hω : ω ∈ survS A n
        · simp [hω]
        · simp [hω]
      rw [e]
      exact condExp_indicator hint2 hS
    filter_upwards [hce, I.sec n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω, fz, frz_eq_of_mem V A hω, frz_eq_of_mem c A hω]
      exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]
      have := hβ n
      positivity

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

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma Fx_lt {n : ℕ} (hn : n < T) : Fx R T n = R.G n := if_pos hn

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunW =====

/-! ### The remaining-budget shifted field on `K` (Lemma G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ}

variable {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

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

lemma sig_pos : 0 < H.sig := (Classical.choose_spec H.hsharp).1

lemma sig_spec {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) :
    H.sig * sNorm ℬ (a - astar) ≤ gap θ astar a := by
  have h := (Classical.choose_spec H.hsharp).2 a (by rw [G1L.Kset_gen H.hgen]; exact ha)
  rw [G1L.sNorm_gen H.hgen] at h
  exact h

lemma norm_le (x : Fin d → ℝ) : ‖x‖ ≤ sNorm ℬ x := by
  rw [← G1L.sNorm_gen H.hgen]; exact T31.norm_le_sNorm H.ne𝒜 H.hspan H.hball x

lemma gap_pos {a : Fin d → ℝ} (ha : a ∈ Kset ℬ) (hne : a ≠ astar) : 0 < gap θ astar a := by
  have h1 : 0 < ‖a - astar‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have h2 := H.norm_le (a - astar)
  exact lt_of_lt_of_le (mul_pos H.sig_pos (lt_of_lt_of_le h1 h2)) (H.sig_spec ha)

/-- duality of the gauge of `𝒮` and the norm `‖·‖_𝒜` -/
lemma abs_dot_le_sNorm (x w : Fin d → ℝ) : |x ⬝ᵥ w| ≤ sNorm ℬ x * setNorm 𝒜 w := by
  rw [← G1L.sNorm_gen H.hgen]
  have hcont : Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w| := by
    simp only [dotProduct]; fun_prop
  have hbdd := (H.h𝒜.image hcont).bddAbove
  have hS : ∀ y ∈ Sset 𝒜, |y ⬝ᵥ w| ≤ setNorm 𝒜 w := by
    intro y hy
    have hcvx : Convex ℝ {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} := by
      have hl : IsLinearMap ℝ (fun x : Fin d → ℝ => x ⬝ᵥ w) :=
        ⟨fun x y => add_dotProduct x y w, fun c x => smul_dotProduct c x w⟩
      have : {x : Fin d → ℝ | |x ⬝ᵥ w| ≤ setNorm 𝒜 w} =
          {v | v ⬝ᵥ w ≤ setNorm 𝒜 w} ∩ {v | -setNorm 𝒜 w ≤ v ⬝ᵥ w} := by
        ext x; simp [abs_le, and_comm]
      rw [this]
      exact (convex_halfSpace_le hl _).inter (convex_halfSpace_ge hl _)
    refine convexHull_min ?_ hcvx hy
    rintro a (ha | ha)
    · exact le_csSup hbdd ⟨a, ha, rfl⟩
    · have : -a ∈ 𝒜 := ha
      show |a ⬝ᵥ w| ≤ _
      have h := le_csSup hbdd ⟨-a, this, rfl⟩
      simp only [neg_dotProduct, abs_neg] at h
      exact h
  have habs : Absorbent ℝ (Sset 𝒜) := absorbent_nhds_zero (T31.Sset_nhds H.ne𝒜 H.hspan)
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _) (hS 0 (by
    have : (0 : Fin d → ℝ) ∈ Sset 𝒜 := mem_of_mem_nhds (T31.Sset_nhds H.ne𝒜 H.hspan)
    exact this))
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  -- for every `r > ‖x‖_S ‖w‖`, `|x·w| ≤ r`
  by_cases hw : setNorm 𝒜 w = 0
  · -- `w` is orthogonal to `𝒜`, hence zero
    have hz : ∀ a ∈ 𝒜, a ⬝ᵥ w = 0 := fun a ha => by
      have h1 : |a ⬝ᵥ w| ≤ setNorm 𝒜 w := le_csSup hbdd ⟨a, ha, rfl⟩
      rw [hw] at h1
      exact abs_nonpos_iff.1 h1
    have hw0 : w = 0 := by
      have : ∀ v ∈ Submodule.span ℝ 𝒜, v ⬝ᵥ w = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem x hx => exact hz x hx
        | zero => simp
        | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
        | smul c x _ hx => rw [smul_dotProduct, hx, smul_zero]
      rw [H.hspan] at this
      ext i
      have := this (Pi.single i 1) trivial
      simpa [single_dotProduct] using this
    rw [hw0, dotProduct_zero, abs_zero]
    rw [hw, mul_zero] at hr; exact hr.le
  · have hwpos : 0 < setNorm 𝒜 w := lt_of_le_of_ne hsn (Ne.symm hw)
    have hlt : gauge (Sset 𝒜) x < r / setNorm 𝒜 w := by
      rw [lt_div_iff₀ hwpos]; unfold sNorm at hr; exact hr
    obtain ⟨b, hb0, hbr, hxb⟩ := exists_lt_of_gauge_lt habs hlt
    obtain ⟨y, hy, rfl⟩ := hxb
    rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hb0]
    calc b * |y ⬝ᵥ w| ≤ b * setNorm 𝒜 w := mul_le_mul_of_nonneg_left (hS y hy) hb0.le
      _ ≤ r / setNorm 𝒜 w * setNorm 𝒜 w := mul_le_mul_of_nonneg_right hbr.le hwpos.le
      _ = r := div_mul_cancel₀ r hwpos.ne'

end Sharp

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma U0_theta {u : Fin d → ℝ} (hu : u ∈ U0 ℬ θ astar) : u ⬝ᵥ θ = 1 := by
  obtain ⟨a, ⟨ha, hne⟩, rfl⟩ := hu
  have h := H.gap_pos ha hne
  unfold ndir; rw [smul_dotProduct, smul_eq_mul]
  exact inv_mul_cancel₀ h.ne'

lemma U0_sNorm {u : Fin d → ℝ} (hu : u ∈ U0 ℬ θ astar) : sNorm ℬ u ≤ H.sig⁻¹ := by
  obtain ⟨a, ⟨ha, hne⟩, rfl⟩ := hu
  have h := H.gap_pos ha hne
  unfold ndir sNorm
  rw [gauge_smul_of_nonneg (inv_nonneg.2 h.le), smul_eq_mul]
  have h2 := H.sig_spec ha
  unfold sNorm at h2
  rw [inv_mul_le_iff₀ h]
  have hs := H.sig_pos
  rw [← div_eq_mul_inv, le_div_iff₀ hs]
  linarith

lemma U0_bdd : U0 ℬ θ astar ⊆ Metric.closedBall 0 H.sig⁻¹ := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (H.norm_le u).trans (H.U0_sNorm hu)

lemma UT_theta {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) : u ⬝ᵥ θ = 1 := by
  have hcl : IsClosed {u : Fin d → ℝ | u ⬝ᵥ θ = 1} :=
    isClosed_eq (by simp only [dotProduct]; fun_prop) continuous_const
  exact closure_minimal (fun v hv => H.U0_theta hv) hcl hu

lemma UT_bdd {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) : ‖u‖ ≤ H.sig⁻¹ := by
  have := closure_minimal H.U0_bdd Metric.isClosed_closedBall hu
  rwa [Metric.mem_closedBall, dist_zero_right] at this

lemma UT_sub_DT : UT ℬ θ astar ⊆ DT ℬ θ astar := fun u hu =>
  ⟨(1, u), ⟨⟨zero_le_one, le_rfl⟩, hu⟩, one_smul _ _⟩

lemma DT_mem {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) :
    ∃ l ∈ Icc (0 : ℝ) 1, ∃ u ∈ UT ℬ θ astar, w = l • u := by
  obtain ⟨⟨l, u⟩, ⟨hl, hu⟩, rfl⟩ := hw
  exact ⟨l, hl, u, hu, rfl⟩

/-- **homogeneous transfer**: a continuous degree-`k` homogeneous bound on centered differences
`φ(a − a*) ≤ Δ(a)^k M` passes to the cone body -/
lemma homog {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) {k : ℕ}
    (hhom : ∀ (c : ℝ) (w : Fin d → ℝ), 0 ≤ c → φ (c • w) = c ^ k * φ w) {M : ℝ} (hM : 0 ≤ M)
    (hK : ∀ a ∈ Kset ℬ, a ≠ astar → φ (a - astar) ≤ gap θ astar a ^ k * M) :
    ∀ w ∈ DT ℬ θ astar, φ w ≤ M := by
  have hU0 : ∀ u ∈ U0 ℬ θ astar, φ u ≤ M := by
    rintro _ ⟨a, ⟨ha, hne⟩, rfl⟩
    have g := H.gap_pos ha hne
    unfold ndir
    rw [hhom _ _ (inv_nonneg.2 g.le), inv_pow]
    rw [inv_mul_le_iff₀ (pow_pos g k)]
    exact hK a ha hne
  have hUT : ∀ u ∈ UT ℬ θ astar, φ u ≤ M := fun u hu =>
    closure_minimal hU0 (isClosed_le hφ continuous_const) hu
  intro w hw
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [hhom _ _ hl0]
  have h1 := hUT u hu
  have h2 : l ^ k ≤ 1 := pow_le_one₀ hl0 hl1
  have h3 : 0 ≤ l ^ k := pow_nonneg hl0 k
  nlinarith

/-- `|u·w| ≤ ‖w‖_𝒜 / ς` on the cone body -/
lemma DT_dot_le (w : Fin d → ℝ) : ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ H.sig⁻¹ * setNorm 𝒜 w := by
  have hsn : 0 ≤ setNorm 𝒜 w := le_trans (abs_nonneg _)
    (le_csSup ((H.h𝒜.image (by simp only [dotProduct]; fun_prop :
      Continuous fun a : Fin d → ℝ => |a ⬝ᵥ w|)).bddAbove) ⟨astar, H.hastar, rfl⟩)
  refine H.homog (φ := fun u => |u ⬝ᵥ w|) (by simp only [dotProduct]; fun_prop)
    (fun c v hc => by rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_nonneg hc, pow_one])
    (by have := H.sig_pos; positivity) ?_
  intro a ha hne
  have h1 := H.abs_dot_le_sNorm (a - astar) w
  have h2 := H.sig_spec ha
  have hs := H.sig_pos
  rw [pow_one]
  calc |(a - astar) ⬝ᵥ w| ≤ sNorm ℬ (a - astar) * setNorm 𝒜 w := h1
    _ ≤ (gap θ astar a / H.sig) * setNorm 𝒜 w := by
        gcongr; rw [le_div_iff₀ hs]; linarith
    _ = gap θ astar a * (H.sig⁻¹ * setNorm 𝒜 w) := by ring

/-- the cone body lies in the span of the centered differences -/
lemma DT_sub_span : DT ℬ θ astar ⊆
    (Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ) : Set (Fin d → ℝ)) := by
  set V := Submodule.span ℝ ((fun a => a - astar) '' Kset ℬ)
  have hV : IsClosed (V : Set (Fin d → ℝ)) := Submodule.closed_of_finiteDimensional V
  have hU0 : U0 ℬ θ astar ⊆ V := by
    rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact V.smul_mem _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  have hUT : UT ℬ θ astar ⊆ V := closure_minimal hU0 hV
  rintro _ ⟨⟨l, u⟩, ⟨-, hu⟩, rfl⟩
  exact V.smul_mem l (hUT hu)

lemma DT_bdd {w : Fin d → ℝ} (hw : w ∈ DT ℬ θ astar) : ‖w‖ ≤ H.sig⁻¹ := by
  obtain ⟨l, ⟨hl0, hl1⟩, u, hu, rfl⟩ := H.DT_mem hw
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0]
  have := H.UT_bdd hu
  have hs : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  nlinarith [norm_nonneg u]

/-- **projective extension (G.306)**: the normalized field is dominated by the centered field -/
lemma DT_span_bound : ∃ Λ1 : ℝ, 0 < Λ1 ∧ ∀ (w : Fin d → ℝ) (M : ℝ),
    (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) → ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M := by
  classical
  set s := (fun a => a - astar) '' Kset ℬ
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent ℝ s
  have : Finite b := hli.finite_of_isNoetherian
  haveI : Fintype b := Fintype.ofFinite b
  set L := Fintype.linearCombination ℝ (fun i : b => (i : Fin d → ℝ))
  have hL : LinearMap.range L = Submodule.span ℝ s := by
    rw [Fintype.range_linearCombination, Subtype.range_coe, hspan]
  obtain ⟨g, hg⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  set gc := LinearMap.toContinuousLinearMap g
  refine ⟨(Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1, add_pos_of_nonneg_of_pos (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) gc.opNorm_nonneg) (inv_nonneg.2 H.sig_pos.le)) one_pos, ?_⟩
  intro w M hM u hu
  have hM0 : 0 ≤ M := by
    have := hM astar H.haK
    simpa using le_trans (abs_nonneg _) this
  have huV : u ∈ LinearMap.range L := by rw [hL]; exact H.DT_sub_span hu
  set c := g ⟨u, huV⟩
  have hLc : L c = u := by
    have := congrArg Subtype.val (LinearMap.congr_fun hg ⟨u, huV⟩)
    simpa [c] using this
  have hc : ‖c‖ ≤ ‖gc‖ * H.sig⁻¹ := by
    have h1 : ‖c‖ ≤ ‖gc‖ * ‖(⟨u, huV⟩ : LinearMap.range L)‖ := gc.le_opNorm _
    have h2 : ‖(⟨u, huV⟩ : LinearMap.range L)‖ = ‖u‖ := rfl
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (H.DT_bdd hu) gc.opNorm_nonneg)
  rw [← hLc, Fintype.linearCombination_apply, sum_dotProduct]
  calc |∑ i : b, (c i • (i : Fin d → ℝ)) ⬝ᵥ w| ≤ ∑ i : b, |(c i • (i : Fin d → ℝ)) ⬝ᵥ w| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : b, ‖c‖ * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [smul_dotProduct, smul_eq_mul, abs_mul]
        obtain ⟨a, ha, hai⟩ := hbs i.2
        have h1 : |(i : Fin d → ℝ) ⬝ᵥ w| ≤ M := by rw [← hai]; exact hM a ha
        have h2 : |c i| ≤ ‖c‖ := by
          have := norm_le_pi_norm c i
          rwa [Real.norm_eq_abs] at this
        exact mul_le_mul h2 h1 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card b : ℝ) * ‖c‖ * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ((Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1) * M := by
        have : (Fintype.card b : ℝ) * ‖c‖ ≤ (Fintype.card b : ℝ) * ‖gc‖ * H.sig⁻¹ + 1 := by
          have := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (Fintype.card b))
          linarith
        exact mul_le_mul_of_nonneg_right this hM0

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

lemma Lam1_eq : ∃ h, Lam1 ℬ θ astar = Classical.choose (p := fun Λ1 : ℝ => 0 < Λ1 ∧
    ∀ (w : Fin d → ℝ) (M : ℝ), (∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) →
      ∀ u ∈ DT ℬ θ astar, |u ⬝ᵥ w| ≤ Λ1 * M) h :=
  ⟨H.DT_span_bound, by unfold Lam1; rw [dif_pos H.DT_span_bound]⟩

lemma Lam1_pos : 0 < Lam1 ℬ θ astar := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).1

lemma Lam1_spec {w : Fin d → ℝ} {M : ℝ} (hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ w| ≤ M) {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) : |u ⬝ᵥ w| ≤ Lam1 ℬ θ astar * M := by
  obtain ⟨h, e⟩ := H.Lam1_eq; rw [e]; exact (Classical.choose_spec h).2 w M hM u hu

lemma kb_ge : 1 ≤ H.kb ∧ H.sig⁻¹ ≤ H.kb ∧ H.sig⁻¹ ^ 2 ≤ H.kb := by
  have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  unfold kb; refine ⟨?_, ?_, ?_⟩ <;> nlinarith

end Sharp

end G26G

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma kappa_facts (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) (ω : Ω) :
    0 ≤ setNorm 𝒜 (R.θs n ω - θ) ∧ setNorm 𝒜 (R.θs n ω - θ) ≤ 2 := by
  have hne𝒜 := H.ne𝒜
  have hθn := (hR n hn).2.2.2.2.2
  refine ⟨setNorm_nonneg H.h𝒜 hne𝒜 _, ?_⟩
  have := setNorm_sub_le H.h𝒜 hne𝒜 (R.θs n ω) θ
  linarith [hθn ω, H.hθ]

lemma dirN_bound (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) :
    ∀ᵐ ω ∂P, |u ⬝ᵥ gv (R.p n ω) (R.X n ω)| ≤
      Lam1 ℬ θ astar * (2 * (gbeta d (n + 1) + G2R.rho d n / gB d)) := by
  filter_upwards [G2R.v_bound_ae H.hd H.hℬ H.hgen H.hspan hR hn] with ω h
  exact H.Lam1_spec (fun a ha => h.2 a ha astar H.haK) hu

lemma thetaN_bound (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {n : ℕ} (hn : n < T) {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) (ω : Ω) : |u ⬝ᵥ R.θs n ω| ≤ H.sig⁻¹ := by
  have h1 := H.DT_dot_le (R.θs n ω) u hu
  have h2 := (hR n hn).2.2.2.2.2 ω
  have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  calc |u ⬝ᵥ R.θs n ω| ≤ H.sig⁻¹ * setNorm 𝒜 (R.θs n ω) := h1
    _ ≤ H.sig⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 this
    _ = H.sig⁻¹ := mul_one _

end Sharp

end G26G


-- ===== Solutions.G26.Scalar =====

/-! ### Killed scalar local moments (Lemma G.22 and the local moments of Lemma G.28) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

lemma SI.Ym' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : Measurable (Y n) :=
  (S.Ym n hn).mono (S.Fle n hn) le_rfl

lemma SI.Im' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : MeasurableSet (I n) :=
  S.Fle n hn _ (S.Im n hn)

lemma SI.kpos_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => Y n ω ^ P)) μ := by
  obtain ⟨r, hr⟩ := S.env n hn
  refine Integrable.of_bound (((S.Ym' hn).pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    (|r| ^ P) ?_
  filter_upwards [hr] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω.trans (le_abs_self _)) _
  · rw [Set.indicator_of_notMem h, abs_zero]; positivity

end G26


-- ===== Solutions.G26.SIFreeze =====

/-! ### Freezing a scalar interface at a predictable success rule (Lemma G.29, (G.653)–(G.659)) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

open Classical in
/-- the freezing index: the first failure of the rule before `n`, or `n` -/
noncomputable def fidx (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) : ℕ :=
  if h : ∃ i, i < n ∧ ω ∉ A i then Nat.find h else n

lemma frz_fidx {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    frz X A n ω = X (fidx A n ω) ω ∧ fidx A n ω ≤ n ∧
      (fidx A n ω = n ∨ ω ∉ A (fidx A n ω)) ∧ ∀ j < fidx A n ω, ω ∈ A j := by
  classical
  unfold fidx
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hmin : ∀ j < Nat.find h, ω ∈ A j := fun j hj => by
      by_contra hj'
      exact Nat.find_min h hj ⟨by have := hspec.1; omega, hj'⟩
    have hsurv : Nat.find h = 0 ∨ ω ∈ survS A (Nat.find h - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact hmin j (by omega)
    exact ⟨frz_stop X A hsurv hspec.2 n hspec.1.le, hspec.1.le, Or.inr hspec.2, hmin⟩
  · push Not at h
    have hs : n = 0 ∨ ω ∈ survS A (n - 1) := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact Or.inl h0
      · right
        simp only [survS, Set.mem_iInter, Finset.mem_range]
        intro j hj; exact h j (by omega)
    exact ⟨frz_eq X A n ω hs, le_rfl, Or.inl rfl, fun j hj => h j hj⟩

lemma frz_before {E : Type*} (X : ℕ → Ω → E) {A : ℕ → Set Ω} {u : ℕ} (hA : ∀ n < u, A n = univ) :
    frz X A u = X u := by
  funext ω
  refine frz_eq X A u ω ?_
  rcases Nat.eq_zero_or_pos u with h | h
  · exact Or.inl h
  · right
    simp only [survS, Set.mem_iInter, Finset.mem_range]
    intro j hj; rw [hA j (by omega)]; trivial

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

end G26


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

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


-- ===== Solutions.G26.RunSIN =====

/-! ### Compensated normalized pointwise variables (Lemma G.28, (G.595)–(G.601)) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma YN_succ (θ : Fin d → ℝ) (l C : ℝ) (τ : ℕ → ℝ) (u : Fin d → ℝ) (n : ℕ) (ω : Ω) :
    YN R θ l C τ u (n + 1) ω - YN R θ l C τ u n ω =
      u ⬝ᵥ R.thetaHat n ω - u ⬝ᵥ (R.θs n ω - θ) + 2 * (τ (n + 1) - τ n) := by
  simp only [YN, cumEst_succ, Ecor_succ, dotProduct_add]; ring

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

lemma EcorN_le {u : Fin d → ℝ} (hu : u ∈ DT ℬ θ astar) (n : ℕ) (ω : Ω) :
    |Ecor R θ u n ω| ≤ H.sig⁻¹ * Acum 𝒜 R θ n ω := by
  unfold Ecor Acum
  rw [Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => H.DT_dot_le _ u hu)

/-- the drift of the compensated normalized variable is exactly `θ·u + 2δ_n` -/
lemma runN_drift (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ} {u : Fin d → ℝ}
    (hu : u ∈ DT ℬ θ astar) (τ : ℕ → ℝ) {n : ℕ} (hnT : n < T) :
    P[fun ω => YN R θ H.sig⁻¹ C τ u (n + 1) ω - YN R θ H.sig⁻¹ C τ u n ω | Fx R T n] =ᵐ[P]
      fun _ => u ⬝ᵥ θ + 2 * (τ (n + 1) - τ n) := by
  have hGle := G2R.G_le hR hnT
  have hcw := H.dirN_bound hR hnT hu
  have hcm := cond_mean H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT u hcw (cθ := H.sig⁻¹)
    (H.thetaN_bound hR hnT hu)
  set g : Ω → ℝ := fun ω => -(u ⬝ᵥ (R.θs n ω - θ)) + 2 * (τ (n + 1) - τ n) with hg
  have hgm : StronglyMeasurable[R.G n] g :=
    (((G2R.meas_dot' measurable_const (((hR n hnT).1.2.2.2.2.2.2.1).sub measurable_const)).neg).add
      measurable_const).stronglyMeasurable
  have hgb : ∀ ω, |g ω| ≤ 2 * H.sig⁻¹ + |2 * (τ (n + 1) - τ n)| := fun ω => by
    have h1 : |u ⬝ᵥ (R.θs n ω - θ)| ≤ 2 * H.sig⁻¹ := by
      refine (H.DT_dot_le _ u hu).trans ?_
      obtain ⟨-, h2⟩ := H.kappa_facts hR hnT ω
      have : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
      nlinarith
    simp only [hg]
    have := abs_add_le (-(u ⬝ᵥ (R.θs n ω - θ))) (2 * (τ (n + 1) - τ n))
    rw [abs_neg] at this
    linarith
  have hfi : Integrable (fun ω => u ⬝ᵥ R.thetaHat n ω) P := by
    have := (unbiased_φ H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR hnT u hcw (φ := fun _ => 1)
      measurable_const (fun _ => by simp)).1
    simpa using this
  have hf2 : Integrable (fun ω => (u ⬝ᵥ R.thetaHat n ω) ^ 2) P := by
    refine Integrable.of_bound (hfi.aestronglyMeasurable.pow 2)
      ((Lam1 ℬ θ astar * (2 * (gbeta d (n + 1) + G2R.rho d n / gB d))) ^ 2) ?_
    filter_upwards [hcw] with ω h
    rw [Real.norm_eq_abs, abs_pow, GRun.thetaHat, dotProduct_smul, smul_eq_mul, abs_mul]
    have hY := (hR n hnT).2.2.2.2.1.1 ω
    exact pow_le_pow_left₀ (by positivity) ((mul_le_of_le_one_left (abs_nonneg _) hY).trans h) 2
  have hsh := (condExp_shift (G := R.G) hGle hfi hf2 hgm hgb).1
  have e1 : (fun ω => YN R θ H.sig⁻¹ C τ u (n + 1) ω - YN R θ H.sig⁻¹ C τ u n ω) =
      fun ω => u ⬝ᵥ R.thetaHat n ω + g ω :=
    funext fun ω => by rw [YN_succ]; simp only [hg]; ring
  rw [e1, Fx_lt hnT]
  filter_upwards [hsh, hcm] with ω h1 h2
  rw [h1, h2]
  simp only [hg]
  rw [dotProduct_sub, dotProduct_comm u θ]; ring

end Sharp

end G26G


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma rdim_le (D : Set (Fin d → ℝ)) : rdim D ≤ d := by
  unfold rdim
  have := Submodule.finrank_le (vectorSpan ℝ D)
  simpa using this

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ}
    (hn : n ≤ T) (P : ℕ) : Integrable (fun ω => absMax D (V n ω) (c n ω) ^ P) μ := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine Integrable.of_bound
    (((I.absMax_meas hn).mono (I.Fle n hn) le_rfl).pow_const P).aestronglyMeasurable (r ^ P) ?_
  filter_upwards [hr, I.N0 n hn] with ω h h0
  have h1 : 0 ≤ absMax D (V n ω) (c n ω) := h0.trans (negMax_le_absMax _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 _)]
  exact pow_le_pow_left₀ h1 h.1 P

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma kk_facts (d : ℕ) : 2 ≤ kk d ∧ 4 ≤ 4 * kk d ∧ Even (4 * kk d) ∧ d ≤ 4 * kk d ∧
    2 ^ 20 * ((4 * kk d : ℕ) : ℝ) ≤ gB d := by
  unfold kk gB
  refine ⟨by omega, by omega, ⟨2 * (1024 * (d + 1)), by ring⟩, by omega, ?_⟩
  push_cast; nlinarith

lemma gbeta_le (d n : ℕ) : gbeta d (n + 1) ≤ (16 * d + 1) * ((n : ℝ) + 1) := by
  unfold gbeta
  have h1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; push_cast; nlinarith
  have h2 : (16 * d : ℝ) ≤ 16 * d * ((n : ℝ) + 1) := by
    have : (0 : ℝ) ≤ 16 * d := by positivity
    nlinarith
  nlinarith

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

/-- **the absolute envelope of the jointly frozen loss-difference field (G.288)** -/
theorem absK_env (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[Fx R T n] (A n)) {n : ℕ} (hn : n ≤ T) :
    ∫ ω, absMax (Kset ℬ) (frz R.cumEst A n ω)
      (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A n ω) ^ (4 * kk d) ∂P ≤
      cK d * ((n : ℝ) + 1) ^ (4 * kk d) := by
  obtain ⟨hk2, hP4, hev, hdP, hB⟩ := kk_facts d
  have I0 := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
  have I := I0.freeze hA (by norm_num) (by norm_num) (fun n => (G2R.gbeta_pos H.hd (n + 1)).le)
    G2R.gB_pos (J' := fun _ => univ) (fun _ _ => MeasurableSet.univ) (fun _ => subset_rfl)
    (fun _ => subset_univ _)
  have h0 : ∀ ω, Gf (Kset ℬ) (frz R.cumEst A) (frz (fun n ω => -(astar ⬝ᵥ R.cumEst n ω)) A)
      (4 * kk d) 0 ω = 0 := by
    intro ω
    unfold Gf fz
    simp only [frz, GRun.cumEst, Finset.range_zero, Finset.sum_empty, dotProduct_zero, neg_zero,
      add_zero]
    rw [zero_pow (by omega)]; simp
  have h := I.absMax_env (by norm_num) le_rfl hP4 hev ((rdim_le _).trans hdP) hB
    (fun n => G2R.gbeta_pos H.hd (n + 1)) (fun n => gbeta_le d n) h0 hn
  simp only [Set.indicator_univ] at h
  refine h.trans ?_
  unfold cK
  have h4 : (4 : ℝ) ^ rdim (Kset ℬ) ≤ 4 ^ d := pow_le_pow_right₀ (by norm_num) (rdim_le _)
  have hC : 0 ≤ Cabs (4 * kk d) (16 * d + 1) (gB d) 0 := by unfold Cabs; positivity
  gcongr

end Sharp

end G26G


-- ===== Solutions.G26.Params =====

/-! ### Thresholds: buffers `τ_s = (s+1)^{7/8} + 4z` and logarithmic gap cutoffs -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26G

open G26 G26R

lemma p78_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x ^ ((7 : ℝ) / 8) ≤ y ^ ((7 : ℝ) / 8) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

lemma p78_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ x ^ ((7 : ℝ) / 8) :=
  Real.one_le_rpow hx (by norm_num)

lemma tauB_mono {z : ℝ} (s : ℕ) : tauB z s ≤ tauB z (s + 1) := by
  unfold tauB
  have := p78_mono (x := (s : ℝ) + 1) (y := ((s + 1 : ℕ) : ℝ) + 1) (by positivity) (by push_cast; linarith)
  linarith

lemma tauB_delta (z : ℝ) (s : ℕ) : tauB z (s + 1) - tauB z s ≤ 1 := by
  unfold tauB
  have h := Real.rpow_add_le_add_rpow (p := (7 : ℝ) / 8) (a := (s : ℝ) + 1) (b := 1)
    (by positivity) zero_le_one (by norm_num) (by norm_num)
  rw [Real.one_rpow] at h
  have e : ((s + 1 : ℕ) : ℝ) + 1 = (s : ℝ) + 1 + 1 := by push_cast; ring
  rw [e]; linarith

lemma tauB_ge {z : ℝ} (hz : 0 ≤ z) (s : ℕ) :
    ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) ≤ tauB z s ∧ 4 * z ≤ tauB z s ∧ 1 ≤ tauB z s := by
  unfold tauB
  have h1 := p78_ge_one (x := (s : ℝ) + 1) (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  refine ⟨by linarith, ?_, by linarith⟩
  have : 0 ≤ ((s : ℝ) + 1) ^ ((7 : ℝ) / 8) := by positivity
  linarith

lemma tauB_pos {z : ℝ} (hz : 0 ≤ z) (s : ℕ) : 0 < tauB z s := by
  linarith [(tauB_ge hz s).2.2]

lemma root8_pow {x : ℝ} (hx : 0 ≤ x) : root8 x ^ 8 = x := by
  unfold root8
  have h1 : Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt (Real.sqrt x) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : Real.sqrt (Real.sqrt x) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  calc Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 8 =
      ((Real.sqrt (Real.sqrt (Real.sqrt x)) ^ 2) ^ 2) ^ 2 := by ring
    _ = x := by rw [h1, h2, h3]

lemma root8_nonneg (x : ℝ) : 0 ≤ root8 x := Real.sqrt_nonneg _

lemma root8_mono {x y : ℝ} (hxy : x ≤ y) : root8 x ≤ root8 y := by
  unfold root8
  exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hxy))

end G26G

namespace G26G

lemma root8_eq_rpow {x : ℝ} (hx : 0 ≤ x) : root8 x = x ^ ((1 : ℝ) / 8) := by
  have h1 : (x ^ ((1 : ℝ) / 8)) ^ (8 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
  have h2 := root8_pow hx
  have hn1 : 0 ≤ x ^ ((1 : ℝ) / 8) := Real.rpow_nonneg hx _
  exact (pow_left_inj₀ (root8_nonneg x) hn1 (by norm_num : (8 : ℕ) ≠ 0)).1 (h2.trans h1.symm)

lemma rpow78_eq {x : ℝ} (hx : 0 ≤ x) : x ^ ((7 : ℝ) / 8) = root8 x ^ 7 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma sqrt_eq_root8 {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x = root8 x ^ 4 := by
  rw [root8_eq_rpow hx, ← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]; norm_num

end G26G


-- ===== Solutions.G26.RefBlock =====

/-! ### Uniform reference control on a block (Lemma G.29) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma add_pow_le_two {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (n : ℕ) :
    (x + y) ^ n ≤ 2 ^ n * (x ^ n + y ^ n) := by
  rcases le_total x y with h | h
  · have h1 : (x + y) ^ n ≤ (2 * y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ x ^ n := pow_nonneg hx n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have h1 : (x + y) ^ n ≤ (2 * x) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    rw [mul_pow] at h1
    have : 0 ≤ y ^ n := pow_nonneg hy n
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]

lemma frz_univ {E : Type*} (X : ℕ → Ω → E) (n : ℕ) : frz X (fun _ => univ) n = X n := by
  funext ω
  obtain ⟨h1, -, h3, -⟩ := frz_fidx X (fun _ => (univ : Set Ω)) n ω
  rcases h3 with h | h
  · rw [h1, h]
  · exact absurd trivial h

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

variable (he : Function.Surjective e)
include he

end Sharp

end G26G


-- ===== Solutions.G26.RefAlg =====

/-! ### Real-variable estimates for the reference block bound -/

open IAFTRL

namespace G26G

lemma tauB_ge_r7 {z : ℝ} (hz : 0 ≤ z) (n : ℕ) : root8 ((n : ℝ) + 1) ^ 7 ≤ tauB z n := by
  rw [← rpow78_eq (by positivity)]; exact (tauB_ge hz n).1

end G26G


-- ===== Solutions.G26.WinMom =====

/-! ### The alive window (Lemma G.28): local per-point moments of the compensated variable -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma thr_win {n : ℕ} {z l kb : ℝ} (hz : 0 ≤ z) (hl : 0 ≤ l) (hkb : 0 ≤ kb)
    (hr : cTw d l kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ tauB z n ∧
    40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1) ≤ tauB z n ^ 2 ∧
    10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1)) / tauB z n ≤ 1 ∧
    ((4 * kk d : ℕ) : ℝ) + 1 ≤ tauB z n ∧ ((4 * kk d : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by
  set r := root8 ((n : ℝ) + 1)
  have hP0 : (0 : ℝ) ≤ ((4 * kk d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hB0 := G2R.gB_pos (d := d)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have t1 : 0 ≤ gB d * (l * (16 * d + 3) + 2) := by positivity
  have t2 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) := by positivity
  have t3 : 0 ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) := by positivity
  have hc1 : 1 ≤ cTw d l kb := by unfold cTw; linarith
  have hr1 : 1 ≤ r := hc1.trans hr
  have hr8 : r ^ 8 = (n : ℝ) + 1 := root8_pow (by positivity)
  have hsq : Real.sqrt (((n + 1 : ℕ) : ℝ)) = r ^ 4 := by
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]; exact sqrt_eq_root8 (by positivity)
  have hg : gbeta d (n + 1) ≤ (16 * d + 1) * r ^ 4 := by
    unfold gbeta; rw [hsq]
    have : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
    nlinarith
  have hg0 : 0 ≤ gbeta d (n + 1) := by unfold gbeta; positivity
  have hτ := tauB_ge_r7 hz n
  have hr4 : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
  have hr47 : r ^ 5 ≤ r ^ 7 := pow_le_pow_right₀ hr1 (by norm_num)
  have h5 : r ^ 4 * r = r ^ 5 := by ring
  -- the pieces of the threshold
  have hc_a : gB d * (l * (16 * d + 3) + 2) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_b : 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_c : 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  have hc_d : ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := by
    refine le_trans ?_ hr; unfold cTw; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the buffer dominates the update magnitude
    have h1 : gbeta d (n + 1) * l + 2 * l + 2 ≤ (l * (16 * d + 3) + 2) * r ^ 4 := by
      have := mul_le_mul_of_nonneg_left hg hl
      nlinarith [mul_nonneg hl hd0]
    calc gB d * (gbeta d (n + 1) * l + 2 * l + 2) ≤ gB d * ((l * (16 * d + 3) + 2) * r ^ 4) :=
          mul_le_mul_of_nonneg_left h1 hB0.le
      _ = gB d * (l * (16 * d + 3) + 2) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_a (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · have h7 : r ^ 14 ≤ tauB z n ^ 2 := by
      rw [show 14 = 7 * 2 by norm_num, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hτ 2
    have hP1 : 0 ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb := by positivity
    calc 40 * (((4 * kk d : ℕ) : ℝ) + 1) * (kb * gbeta d (n + 1)) * ((n : ℝ) + 1)
        = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * gbeta d (n + 1) * r ^ 8 := by rw [hr8]; ring
      _ ≤ 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * ((16 * d + 1) * r ^ 4) * r ^ 8 := by gcongr
      _ = 40 * (((4 * kk d : ℕ) : ℝ) + 1) * kb * (16 * d + 1) * r ^ 12 := by ring
      _ ≤ r * r ^ 12 := mul_le_mul_of_nonneg_right hc_b (by positivity)
      _ = r ^ 13 := by ring
      _ ≤ r ^ 14 := pow_le_pow_right₀ hr1 (by norm_num)
      _ ≤ tauB z n ^ 2 := h7
  · have hτ0 : 0 < tauB z n := tauB_pos hz n
    rw [div_le_one hτ0]
    calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
        ≤ 10 * ((4 * kk d : ℕ) : ℝ) * kb * ((16 * d + 1) * r ^ 4) := by
          have : 10 * (((4 * kk d : ℕ) : ℝ) - 1) ≤ 10 * ((4 * kk d : ℕ) : ℝ) := by linarith
          calc 10 * (((4 * kk d : ℕ) : ℝ) - 1) * (kb * gbeta d (n + 1))
              ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * gbeta d (n + 1)) :=
                mul_le_mul_of_nonneg_right this (mul_nonneg hkb hg0)
            _ ≤ 10 * ((4 * kk d : ℕ) : ℝ) * (kb * ((16 * d + 1) * r ^ 4)) := by gcongr
            _ = _ := by ring
      _ = 10 * ((4 * kk d : ℕ) : ℝ) * kb * (16 * d + 1) * r ^ 4 := by ring
      _ ≤ r * r ^ 4 := mul_le_mul_of_nonneg_right hc_c (by positivity)
      _ = r ^ 5 := by ring
      _ ≤ tauB z n := hr47.trans hτ
  · calc ((4 * kk d : ℕ) : ℝ) + 1 ≤ r := hc_d
      _ ≤ r ^ 7 := le_self_pow₀ hr1 (by norm_num)
      _ ≤ tauB z n := hτ
  · have : r ≤ r ^ 8 := le_self_pow₀ hr1 (by norm_num)
    rw [hr8] at this; linarith

lemma kk_num : ((4 * kk d : ℕ) : ℝ) = 4096 * ((d : ℝ) + 1) := by
  have hkk : kk d = 1024 * (d + 1) := by unfold kk; rfl
  rw [hkk]; push_cast; ring

lemma root8_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : root8 (x * y) = root8 x * root8 y := by
  unfold root8
  rw [Real.sqrt_mul hx, Real.sqrt_mul (Real.sqrt_nonneg _), Real.sqrt_mul (Real.sqrt_nonneg _)]

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar) (he : Function.Surjective e)
include H he

omit he in
lemma cTw_ge (n : ℕ) {z : ℝ} (hz : 0 ≤ z) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1)) :
    gB d * (gbeta d (n + 1) * H.sig⁻¹ + 2 * H.sig⁻¹ + 2) ≤ tauB z n :=
  (thr_win hz (inv_nonneg.2 H.sig_pos.le) (by linarith [H.kb_ge.1]) hr).1

omit he in
lemma cTw_mono {m n : ℕ} (hmn : m ≤ n) (hr : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    cTw d H.sig⁻¹ H.kb ≤ root8 ((n : ℝ) + 1) :=
  hr.trans (root8_mono (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                           linarith))

omit he in
/-- the compensated scalar interface on the window -/
theorem win_SI (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar) {z : ℝ}
    (hz : 0 ≤ z) {m t : ℕ} (ht : t ≤ T) (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) :
    SI P (Fx R T) (YN R θ H.sig⁻¹ C (tauB z) u)
      (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) m t (tauB z)
      (fun n => H.kb * gbeta d (n + 1)) (gB d) :=
  H.runN_SI he hR hcor (H.UT_sub_DT hu) (fun n => tauB_pos hz n) tauB_mono (tauB_delta z) ht
    (fun n hn => H.cTw_ge n hz (H.cTw_mono hn hmc))

set_option maxHeartbeats 1000000 in
omit he in
/-- **local positive moment (G.568)**: `E[I_t Y_t^P] ≤ (8(t+1))^P` once `(m+1)/(t+1)` is small -/
theorem win_pos (he : Function.Surjective e) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) {C : ℝ}
    (hC : 0 ≤ C) (hcor : IsCorruptedG P 𝒜 θ C T R) {u : Fin d → ℝ} (hu : u ∈ UT ℬ θ astar)
    {z : ℝ} (hz : 0 ≤ z) {m t : ℕ} (hmt : m ≤ t) (htT : t < T)
    (hmc : cTw d H.sig⁻¹ H.kb ≤ root8 ((m : ℝ) + 1)) (hlC : H.sig⁻¹ * C ≤ (m : ℝ) + 1)
    (hzt : z ≤ ((t : ℝ) + 1) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ^ 7)
    (hξ : (2 * (Lam1 ℬ θ astar * max 1 (cK d) + 4) + 16) * root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) ≤ 1) :
    kpos P (YN R θ H.sig⁻¹ C (tauB z) u) (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m)
      (4 * kk d) t ≤ (8 * ((t : ℝ) + 1)) ^ (4 * kk d) := by
  have S := H.win_SI he hR hcor hu hz (t := t) htT.le hmc
  have hl : 0 ≤ H.sig⁻¹ := inv_nonneg.2 H.sig_pos.le
  have hkb : 0 ≤ H.kb := by linarith [H.kb_ge.1]
  have hthr := fun n (hn : m ≤ n) => thr_win (d := d) (n := n) hz hl hkb (H.cTw_mono hn hmc)
  have hkn := kk_num (d := d)
  have hBd : gB d = 2 ^ 36 * ((d : ℝ) + 1) := rfl
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hmt' : (m : ℝ) + 1 ≤ (t : ℝ) + 1 := by linarith [(by exact_mod_cast hmt : (m : ℝ) ≤ t)]
  have hL0 := H.Lam1_pos
  set cK1 := max 1 (cK d) with hcK1
  have hcK1 : 1 ≤ cK1 := le_max_left _ _
  have hcKle : cK d ≤ cK1 ^ (4 * kk d) :=
    (le_max_right _ _).trans (le_self_pow₀ hcK1 (by have := (kk_facts d).1; omega))
  set w0 := 2 * (Lam1 ℬ θ astar * cK1 * ((m : ℝ) + 1) + 2 * (H.sig⁻¹ * C) + 2 * tauB z m) with hw0def
  have hτm0 := tauB_pos hz m
  have hw0 : 0 < w0 := by rw [hw0def]; have := mul_nonneg hl hC; positivity
  -- the initial moment
  have hW0 : kpos P (YN R θ H.sig⁻¹ C (tauB z) u)
      (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m) (4 * kk d) m ≤ w0 ^ (4 * kk d) := by
    have IK := runK_FI H.hd H.h𝒜 H.hℬ H.hgen H.hspan hR H.haK
    have hmT : m ≤ T := hmt.trans htT.le
    have hK := H.absK_env hR (A := fun _ => univ) (fun _ _ => MeasurableSet.univ) hmT
    simp only [frz_univ] at hK
    have hint := IK.absMax_int hmT (4 * kk d)
    set RX := fun ω => absMax (Kset ℬ) (R.cumEst m ω) (-(astar ⬝ᵥ R.cumEst m ω)) with hRX
    have hRX0 : ∀ ω, 0 ≤ RX ω := fun ω =>
      (abs_nonneg _).trans (abs_le_absMax H.Kc H.haK (R.cumEst m ω) (-(astar ⬝ᵥ R.cumEst m ω)))
    have hb0 : 0 ≤ 2 * (H.sig⁻¹ * C) + 2 * tauB z m := by have := mul_nonneg hl hC; positivity
    have hpt : ∀ᵐ ω ∂P, (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m m).indicator
        (fun ω => YN R θ H.sig⁻¹ C (tauB z) u m ω ^ (4 * kk d)) ω ≤
        2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * RX ω ^ (4 * kk d) +
          (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) := by
      filter_upwards [S.low m le_rfl hmt, Acum_le H.h𝒜 H.ne𝒜 hcor] with ω hlow hA
      obtain ⟨hA0, hAC⟩ := hA m hmT
      have hbd : 0 ≤ 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * RX ω ^ (4 * kk d) +
          (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) := by
        have := hRX0 ω; positivity
      by_cases hI : ω ∈ IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m m
      · rw [indicator_of_mem hI]
        have hY0 : 0 ≤ YN R θ H.sig⁻¹ C (tauB z) u m ω := le_trans hτm0.le (hlow hI)
        have hM : ∀ a ∈ Kset ℬ, |(a - astar) ⬝ᵥ R.cumEst m ω| ≤ RX ω := by
          intro a ha
          have := abs_le_absMax H.Kc ha (R.cumEst m ω) (-(astar ⬝ᵥ R.cumEst m ω))
          rwa [sub_dotProduct, sub_eq_add_neg]
        have h1 := H.Lam1_spec hM (H.UT_sub_DT hu)
        have h2 := H.EcorN_le (H.UT_sub_DT hu) (R := R) m ω
        have h3 : H.sig⁻¹ * Acum 𝒜 R θ m ω ≤ H.sig⁻¹ * C := mul_le_mul_of_nonneg_left hAC hl
        have hYle : YN R θ H.sig⁻¹ C (tauB z) u m ω ≤
            Lam1 ℬ θ astar * RX ω + (2 * (H.sig⁻¹ * C) + 2 * tauB z m) := by
          unfold YN
          have := le_abs_self (u ⬝ᵥ R.cumEst m ω)
          have := neg_abs_le (Ecor R θ u m ω)
          nlinarith
        calc YN R θ H.sig⁻¹ C (tauB z) u m ω ^ (4 * kk d)
            ≤ (Lam1 ℬ θ astar * RX ω + (2 * (H.sig⁻¹ * C) + 2 * tauB z m)) ^ (4 * kk d) :=
              pow_le_pow_left₀ hY0 hYle _
          _ ≤ 2 ^ (4 * kk d) * ((Lam1 ℬ θ astar * RX ω) ^ (4 * kk d) +
                (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) :=
              add_pow_le_two (mul_nonneg hL0.le (hRX0 ω)) hb0 _
          _ = _ := by rw [mul_pow]
      · rw [indicator_of_notMem hI]; exact hbd
    have hint2 : Integrable (fun ω => 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * RX ω ^ (4 * kk d) +
        (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d))) P :=
      ((hint.const_mul _).add (integrable_const _)).const_mul _
    calc kpos P (YN R θ H.sig⁻¹ C (tauB z) u) (IN 𝒜 ℬ e (js ℬ e astar) R θ astar H.sig⁻¹ C (tauB z) m)
          (4 * kk d) m
        ≤ ∫ ω, 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * RX ω ^ (4 * kk d) +
            (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) ∂P :=
          integral_mono_ae (S.kpos_int hmt _) hint2 hpt
      _ = 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * ∫ ω, RX ω ^ (4 * kk d) ∂P +
            (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) := by
          rw [integral_const_mul, integral_add (hint.const_mul _) (integrable_const _),
            integral_const, integral_const_mul]
          simp only [probReal_univ, one_smul]
          rfl
      _ ≤ 2 ^ (4 * kk d) * (Lam1 ℬ θ astar ^ (4 * kk d) * (cK d * ((m : ℝ) + 1) ^ (4 * kk d)) +
            (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) := by gcongr
      _ ≤ 2 ^ (4 * kk d) * ((Lam1 ℬ θ astar * cK1 * ((m : ℝ) + 1)) ^ (4 * kk d) +
            (2 * (H.sig⁻¹ * C) + 2 * tauB z m) ^ (4 * kk d)) := by
          gcongr
          rw [mul_pow, mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcKle (by positivity))
            (by positivity)
      _ ≤ 2 ^ (4 * kk d) * (Lam1 ℬ θ astar * cK1 * ((m : ℝ) + 1) +
            (2 * (H.sig⁻¹ * C) + 2 * tauB z m)) ^ (4 * kk d) :=
          mul_le_mul_of_nonneg_left (pow_add_pow_le (by positivity) hb0
            (by have := (kk_facts d).1; omega)) (by positivity)
      _ = w0 ^ (4 * kk d) := by rw [hw0def, mul_pow]; ring_nf
  have h := S.pos_moment (P := 4 * kk d) (by have := (kk_facts d).1; omega)
    (by rw [hkn, hBd]; nlinarith) hmt le_rfl (A := 4) (by norm_num) (fun _ => 3)
    (fun _ => by norm_num)
    (fun n hmn hnt => by
      filter_upwards [H.runN_drift hR (C := C) (H.UT_sub_DT hu) (tauB z) (hnt.trans htT)]
        with ω hω _
      rw [hω, H.UT_theta hu]
      have := tauB_delta z n
      linarith)
    (fun s hms _ => by have := (hthr s hms).2.2.1; push_cast at this ⊢; linarith)
    (fun n => mul_nonneg hkb (by unfold gbeta; positivity)) hw0 hW0
  -- the deterministic algebra
  set δ := 2 * (((4 * kk d : ℕ) : ℝ) - 1) / gB d with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ, hkn, hBd]; apply div_nonneg _ (by positivity); nlinarith
  have hδ1 : 2 * δ ≤ 1 / 8 := by
    rw [hδ, hkn, hBd, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hA5 : 4 * ((t : ℝ) + 1) / (1 - δ) ≤ 5 * ((t : ℝ) + 1) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  set ξ := root8 (((m : ℝ) + 1) / ((t : ℝ) + 1)) with hξdef
  have hx0 : 0 ≤ ((m : ℝ) + 1) / ((t : ℝ) + 1) := by positivity
  have hξ0 : 0 < ξ := by
    rw [hξdef, root8_eq_rpow hx0]; exact Real.rpow_pos_of_pos (by positivity) _
  have hξ8 : ξ ^ 8 = ((m : ℝ) + 1) / ((t : ℝ) + 1) := root8_pow hx0
  have hξ1 : ξ ≤ 1 := by
    have : ((m : ℝ) + 1) / ((t : ℝ) + 1) ≤ 1 := (div_le_one ht1).2 hmt'
    have h := root8_mono this
    rwa [show root8 1 = 1 by unfold root8; simp] at h
  have hR1 : 1 ≤ ((t : ℝ) + 1) / ((m : ℝ) + 1) := by rw [le_div_iff₀ hm1]; linarith
  have hpow : (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * δ) ≤ ξ⁻¹ := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hR1 hδ1
    refine h1.trans (le_of_eq ?_)
    rw [← root8_eq_rpow (by positivity), hξdef]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← root8_mul (by positivity) hx0, div_mul_div_comm, mul_comm ((t : ℝ) + 1),
      div_self (by positivity)]
    unfold root8; simp
  have hτm : tauB z m ≤ ((m : ℝ) + 1) + 4 * z := by
    unfold tauB
    have := Real.rpow_le_rpow_of_exponent_le (x := (m : ℝ) + 1)
      (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) (show (7 : ℝ) / 8 ≤ 1 by norm_num)
    rw [Real.rpow_one] at this; linarith
  have hm8 : (m : ℝ) + 1 = ξ ^ 8 * ((t : ℝ) + 1) := by rw [hξ8, div_mul_cancel₀ _ ht1.ne']
  have hw0le : w0 ≤ (2 * (Lam1 ℬ θ astar * cK1 + 4) * ξ ^ 8 + 16 * ξ ^ 7) * ((t : ℝ) + 1) := by
    rw [hw0def]
    have : 2 * (Lam1 ℬ θ astar * cK1 * ((m : ℝ) + 1) + 2 * (H.sig⁻¹ * C) + 2 * tauB z m) ≤
        2 * (Lam1 ℬ θ astar * cK1 + 4) * ((m : ℝ) + 1) + 16 * z := by linarith
    calc _ ≤ 2 * (Lam1 ℬ θ astar * cK1 + 4) * ((m : ℝ) + 1) + 16 * z := this
      _ ≤ 2 * (Lam1 ℬ θ astar * cK1 + 4) * ((m : ℝ) + 1) + 16 * (((t : ℝ) + 1) * ξ ^ 7) := by
          linarith [hzt]
      _ = _ := by rw [hm8]; ring
  have hfin : w0 * ξ⁻¹ ≤ (t : ℝ) + 1 := by
    have h7 : ξ ^ 7 ≤ ξ := pow_le_of_le_one hξ0.le hξ1 (by norm_num)
    have h6 : ξ ^ 6 ≤ ξ := pow_le_of_le_one hξ0.le hξ1 (by norm_num)
    have hLc : 0 ≤ Lam1 ℬ θ astar * cK1 + 4 := by positivity
    calc w0 * ξ⁻¹ ≤ (2 * (Lam1 ℬ θ astar * cK1 + 4) * ξ ^ 8 + 16 * ξ ^ 7) * ((t : ℝ) + 1) * ξ⁻¹ :=
          mul_le_mul_of_nonneg_right hw0le (by positivity)
      _ = (2 * (Lam1 ℬ θ astar * cK1 + 4) * (ξ ^ 8 * ξ⁻¹) + 16 * (ξ ^ 7 * ξ⁻¹)) * ((t : ℝ) + 1) := by ring
      _ = (2 * (Lam1 ℬ θ astar * cK1 + 4) * ξ ^ 7 + 16 * ξ ^ 6) * ((t : ℝ) + 1) := by
          have e8 : ξ ^ 8 * ξ⁻¹ = ξ ^ 7 := by
            rw [pow_succ, mul_assoc, mul_inv_cancel₀ hξ0.ne', mul_one]
          have e7 : ξ ^ 7 * ξ⁻¹ = ξ ^ 6 := by
            rw [pow_succ, mul_assoc, mul_inv_cancel₀ hξ0.ne', mul_one]
          rw [e8, e7]
      _ ≤ ((2 * (Lam1 ℬ θ astar * cK1 + 4) + 16) * ξ) * ((t : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ ht1.le
          have a1 := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 2 * (Lam1 ℬ θ astar * cK1 + 4))
          have a2 := mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 16)
          linarith
      _ ≤ 1 * ((t : ℝ) + 1) := mul_le_mul_of_nonneg_right hξ ht1.le
      _ = (t : ℝ) + 1 := one_mul _
  have hw0p : w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * δ) ≤ (t : ℝ) + 1 :=
    (mul_le_mul_of_nonneg_left hpow hw0.le).trans hfin
  have hX : 4 * ((t : ℝ) + 1) / (1 - δ) + w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * δ) ≤
      8 * ((t : ℝ) + 1) := by linarith
  have hX0 : 0 ≤ 4 * ((t : ℝ) + 1) / (1 - δ) + w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * δ) :=
    add_nonneg (div_nonneg (by positivity) (by linarith))
      (mul_nonneg hw0.le (Real.rpow_nonneg (by positivity) _))
  refine h.trans (pow_le_pow_left₀ ?_ ?_ _)
  · exact hX0
  · exact hX

end Sharp

end G26G


theorem _root_.solution : type_of% @G26G.Sharp.win_pos := @G26G.Sharp.win_pos
