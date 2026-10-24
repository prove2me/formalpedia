-- Prove2me | solution 1 for DirectedOpinion.NoMemory.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T06:15:53.448825+00:00
-- url     : https://prove2.me/submissions/66fbdb8d-09ae-4437-b757-aea80bf0ac8d

import Mathlib
import Definitions.Def_DirectedOpinion_NoMemory_Setting
open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace P03a
open DirectedOpinion.NoMemory

/-! ## Generic lemmas -/

lemma meas_rangeSum {α : Type*} {mα : MeasurableSpace α} (n : α → ℕ) (g : ℕ → α → ℝ)
    (hn : Measurable n) (hg : ∀ j, Measurable (g j)) :
    Measurable (fun a => ∑ j ∈ Finset.range (n a), g j a) := by
  have h : Measurable (fun p : α × ℕ => ∑ j ∈ Finset.range p.2, g j p.1) :=
    measurable_from_prod_countable_left
      (fun k => Finset.measurable_sum (Finset.range k) (fun j _ => hg j))
  exact h.comp (measurable_id.prodMk hn)

lemma intg_of_bdd {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → ℝ} (hf : Measurable f) (B : ℝ) (h : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using h ω))

lemma indep_fubini {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → α} {V : Ω → β}
    (hYV : IndepFun Y V P) (hY : Measurable Y) (hV : Measurable V)
    {F : α × β → ℝ} (hF : Measurable F) (hint : Integrable (fun ω => F (Y ω, V ω)) P)
    {g : α → ℝ} (hg : Measurable g) (hFg : ∀ a, ∫ ω, F (a, V ω) ∂P = g a) :
    ∫ ω, F (Y ω, V ω) ∂P = ∫ ω, g (Y ω) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hV.aemeasurable).1 hYV
  have hYVm : Measurable (fun ω => (Y ω, V ω)) := hY.prodMk hV
  have e1 : ∫ ω, F (Y ω, V ω) ∂P = ∫ z, F z ∂(P.map (fun ω => (Y ω, V ω))) :=
    (integral_map hYVm.aemeasurable hF.aestronglyMeasurable).symm
  have hintF : Integrable F ((P.map Y).prod (P.map V)) := by
    rw [← hmap]; exact (integrable_map_measure hF.aestronglyMeasurable hYVm.aemeasurable).2 hint
  rw [e1, hmap, integral_prod F hintF]
  have e2 : ∀ a, ∫ b, F (a, b) ∂(P.map V) = g a := by
    intro a
    have hm : Measurable (fun b => F (a, b)) := hF.comp measurable_prodMk_left
    rw [integral_map hV.aemeasurable hm.aestronglyMeasurable]
    exact hFg a
  simp_rw [e2]
  exact integral_map hY.aemeasurable hg.aestronglyMeasurable

lemma sq_expand {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (s : Finset ℕ) (a0 : ℝ) (a : ℕ → ℝ) (D : ℕ → Ω → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hD : ∀ j, Measurable (D j)) (hB : ∀ j ω, |D j ω| ≤ B)
    (h0 : ∀ j, ∫ ω, D j ω ∂P = 0)
    (hind : ∀ j j', j ≠ j' → ∫ ω, D j ω * D j' ω ∂P = 0) :
    ∫ ω, (a0 + ∑ j ∈ s, a j * D j ω) ^ 2 ∂P
      = a0 ^ 2 + ∑ j ∈ s, a j ^ 2 * ∫ ω, D j ω ^ 2 ∂P := by
  have hI : ∀ j, Integrable (D j) P := fun j => intg_of_bdd (hD j) B (hB j)
  have hI2 : ∀ j j', Integrable (fun ω => D j ω * D j' ω) P := fun j j' =>
    intg_of_bdd ((hD j).mul (hD j')) (B * B) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hB j ω) (hB j' ω) (abs_nonneg _) hB0)
  have expand : ∀ ω, (a0 + ∑ j ∈ s, a j * D j ω) ^ 2 = a0 ^ 2
      + (2 * a0 * ∑ j ∈ s, a j * D j ω
      + ∑ j ∈ s, ∑ j' ∈ s, (a j * a j') * (D j ω * D j' ω)) := by
    intro ω
    have : (∑ j ∈ s, a j * D j ω) ^ 2 = ∑ j ∈ s, ∑ j' ∈ s, (a j * a j') * (D j ω * D j' ω) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => by ring))
    rw [add_sq, this]; ring
  rw [integral_congr_ae (ae_of_all _ expand)]
  have i1 : Integrable (fun ω => 2 * a0 * ∑ j ∈ s, a j * D j ω) P :=
    (integrable_finsetSum _ (fun j _ => (hI j).const_mul (a j))).const_mul _
  have i2 : Integrable (fun ω => ∑ j ∈ s, ∑ j' ∈ s, (a j * a j') * (D j ω * D j' ω)) P :=
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun j' _ => (hI2 j j').const_mul _))
  have i12 : Integrable (fun ω => 2 * a0 * ∑ j ∈ s, a j * D j ω
      + ∑ j ∈ s, ∑ j' ∈ s, (a j * a j') * (D j ω * D j' ω)) P := i1.add i2
  rw [integral_add (integrable_const _) i12, integral_add i1 i2, integral_const,
    integral_const_mul, integral_finsetSum _ (fun j _ => (hI j).const_mul (a j)),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _
      (fun j' _ => (hI2 j j').const_mul _))]
  have hU : P.real Set.univ = 1 := by simp
  simp only [integral_const_mul, h0, mul_zero, Finset.sum_const_zero, zero_add,
    hU, smul_eq_mul, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [integral_finsetSum _ (fun j' _ => (hI2 j j').const_mul _)]
  rw [Finset.sum_eq_single j]
  · simp only [integral_const_mul, ← sq]
  · intro j' _ hne
    rw [integral_const_mul, hind j j' (Ne.symm hne), mul_zero]
  · intro h; exact absurd hj h

/-! ## Deterministic tree lemmas -/

lemma treeOp_zero_succ (n : Label → ℕ) (w : Label → ℕ → ℝ) (f : Label → ℝ) (s : ℕ)
    (i : Label) :
    (treeOp n w 0)^[s+1] f i
      = ∑ j ∈ Finset.range (n i), w i j * (treeOp n w 0)^[s] f (i ++ [j]) := by
  rw [Function.iterate_succ_apply']; simp [treeOp]

lemma treeOp_iter_bound (n : Label → ℕ) (w : Label → ℕ → ℝ) (c : ℝ)
    (hw0 : ∀ i j, 0 ≤ w i j) (hws : ∀ i, ∑ j ∈ Finset.range (n i), w i j ≤ c) (s : ℕ) :
    ∀ (f : Label → ℝ) (B : ℝ), (∀ i, |f i| ≤ B) → ∀ i, |(treeOp n w 0)^[s] f i| ≤ c ^ s * B := by
  induction s with
  | zero => intro f B hf i; simpa using hf i
  | succ s ih =>
    intro f B hf i
    rw [Function.iterate_succ_apply]
    have h1 : ∀ i, |treeOp n w 0 f i| ≤ c * B := by
      intro i
      have hB : 0 ≤ B := le_trans (abs_nonneg _) (hf i)
      simp only [treeOp, zero_mul, add_zero]
      calc |∑ j ∈ Finset.range (n i), w i j * f (i ++ [j])|
          ≤ ∑ j ∈ Finset.range (n i), |w i j * f (i ++ [j])| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (n i), w i j * B := Finset.sum_le_sum (fun j _ => by
            rw [abs_mul, abs_of_nonneg (hw0 i j)]
            exact mul_le_mul_of_nonneg_left (hf _) (hw0 i j))
        _ = (∑ j ∈ Finset.range (n i), w i j) * B := by rw [Finset.sum_mul]
        _ ≤ c * B := mul_le_mul_of_nonneg_right (hws i) hB
    have := ih (treeOp n w 0 f) (c * B) h1 i
    rw [pow_succ, mul_assoc]; exact this

/-! ## The model -/

section model
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]

noncomputable def A (mk : MarkFns M) (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ)
    (ζ : M → ℝ → ℝ) (c d : ℝ) (b : Label) (s T : ℕ) (ω : Ω) : ℝ :=
  (treeOp (fun i => mk.N (X i ω)) (fun i j => mk.C (X i ω) j) 0)^[s]
    (fun i => W mk X U ζ c d i T ω) b

noncomputable def Rp (mk : MarkFns M) (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ)
    (ζ : M → ℝ → ℝ) (c d : ℝ) (b : Label) (t0 : ℕ) (ω : Ω) : ℝ :=
  ∑' s, A mk X U ζ c d b s (t0 + s) ω

variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ζ : M → ℝ → ℝ} {c d : ℝ}

lemma wsum_le (hgw : GWModel P mk X U ζ c d) (x : M) :
    ∑ j ∈ Finset.range (mk.N x), mk.C x j ≤ c := by
  rcases Nat.eq_zero_or_pos (mk.N x) with h | h
  · simp [h, hgw.c_nonneg]
  · exact (hgw.weights_sum x h).le

lemma wsum_nonneg (hgw : GWModel P mk X U ζ c d) (x : M) :
    0 ≤ ∑ j ∈ Finset.range (mk.N x), mk.C x j :=
  Finset.sum_nonneg (fun j _ => hgw.weights_nonneg x j)

lemma W_bound (hgw : GWModel P mk X U ζ c d) (i : Label) (T : ℕ) (ω : Ω) :
    |W mk X U ζ c d i T ω| ≤ 1 := by
  have hz := hgw.ζ_mem (X i ω) (U i T ω)
  have hq := hgw.Q_mem (X i ω)
  have hs1 := wsum_le hgw (X i ω)
  have hs0 := wsum_nonneg hgw (X i ω)
  have hZ : |Z X U ζ i T ω| ≤ 1 := abs_le.2 ⟨hz.1, hz.2⟩
  have hQ : |mk.Q (X i ω)| ≤ 1 := abs_le.2 ⟨hq.1, hq.2⟩
  have hd := hgw.d_pos
  have hc := hgw.c_nonneg
  have hcd := hgw.cd_le_one
  unfold W
  set S := ∑ j ∈ Finset.range (mk.N (X i ω)), mk.C (X i ω) j
  have h1 : |c - S| ≤ c := abs_le.2 ⟨by linarith, by linarith⟩
  calc |d * Z X U ζ i T ω + mk.Q (X i ω) * (c - S)|
      ≤ |d * Z X U ζ i T ω| + |mk.Q (X i ω) * (c - S)| := abs_add_le _ _
    _ = d * |Z X U ζ i T ω| + |mk.Q (X i ω)| * |c - S| := by
        rw [abs_mul, abs_mul, abs_of_pos hd]
    _ ≤ d * 1 + 1 * c := by
        gcongr
    _ ≤ 1 := by linarith

lemma A_bound (hgw : GWModel P mk X U ζ c d) (b : Label) (s T : ℕ) (ω : Ω) :
    |A mk X U ζ c d b s T ω| ≤ c ^ s := by
  have := treeOp_iter_bound (fun i => mk.N (X i ω)) (fun i j => mk.C (X i ω) j) c
    (fun i j => hgw.weights_nonneg _ j) (fun i => wsum_le hgw _) s
    (fun i => W mk X U ζ c d i T ω) 1 (fun i => W_bound hgw i T ω) b
  simpa [A] using this

lemma A_summable (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) (ω : Ω) :
    Summable (fun s => A mk X U ζ c d b s (t0 + s) ω) :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one hgw.c_nonneg hgw.c_lt_one)
    (fun s => by rw [Real.norm_eq_abs]; exact A_bound hgw b s _ ω)

lemma Rp_bound (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) (ω : Ω) :
    |Rp mk X U ζ c d b t0 ω| ≤ (1 - c)⁻¹ := by
  have := tsum_of_norm_bounded (hasSum_geometric_of_lt_one hgw.c_nonneg hgw.c_lt_one)
    (fun s => by rw [Real.norm_eq_abs]; exact A_bound hgw b s (t0 + s) ω)
  rw [Real.norm_eq_abs] at this
  exact this

lemma A_zero (b : Label) (T : ℕ) (ω : Ω) :
    A mk X U ζ c d b 0 T ω = W mk X U ζ c d b T ω := by
  simp [A]

lemma A_succ (b : Label) (s T : ℕ) (ω : Ω) :
    A mk X U ζ c d b (s + 1) T ω
      = ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * A mk X U ζ c d (b ++ [j]) s T ω := by
  unfold A; rw [treeOp_zero_succ]

lemma Rp_rec (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) (ω : Ω) :
    Rp mk X U ζ c d b t0 ω = W mk X U ζ c d b t0 ω
      + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω := by
  unfold Rp
  rw [(A_summable hgw b t0 ω).tsum_eq_zero_add]
  rw [Nat.add_zero, A_zero]
  congr 1
  have e : ∀ s, A mk X U ζ c d b (s + 1) (t0 + (s + 1)) ω
      = ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j * A mk X U ζ c d (b ++ [j]) s (t0 + 1 + s) ω := by
    intro s
    rw [A_succ]
    have : t0 + (s + 1) = t0 + 1 + s := by omega
    rw [this]
  simp_rw [e]
  rw [Summable.tsum_finsetSum (fun j _ =>
    (A_summable hgw (b ++ [j]) (t0 + 1) ω).mul_left _)]
  exact Finset.sum_congr rfl (fun j _ => tsum_mul_left)

lemma Rstar_eq (hcd : c + d = 1) (ω : Ω) :
    Rstar mk X U ζ c d ω = Rp mk X U ζ c d [] 0 ω := by
  have h : (1 - c - d) = 0 := by linarith
  simp only [Rstar, rootOpinion, Rp, A, h, zero_add]

/-! ## sigma-algebras of label sets -/

def fam (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ) : Label ⊕ (Label × ℕ) → MeasurableSpace Ω
  | Sum.inl i => MeasurableSpace.comap (X i) inferInstance
  | Sum.inr p => MeasurableSpace.comap (U p.1 p.2) inferInstance

def key : Label ⊕ (Label × ℕ) → Label
  | Sum.inl i => i
  | Sum.inr p => p.1

def sg (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ) (S : Set Label) : MeasurableSpace Ω :=
  ⨆ k ∈ key ⁻¹' S, fam X U k

def sub (b : Label) : Set Label := {t | b <+: t}

def csub (b : Label) : Set Label := {t | ∃ j, b ++ [j] <+: t}

lemma mem_sub_self (b : Label) : b ∈ sub b := List.prefix_refl b

lemma sub_child_subset (b : Label) (j : ℕ) : sub (b ++ [j]) ⊆ sub b :=
  fun _ ht => (List.prefix_append b [j]).trans ht

lemma sub_child_csub (b : Label) (j : ℕ) : sub (b ++ [j]) ⊆ csub b :=
  fun _ ht => ⟨j, ht⟩

lemma disj_self_csub (b : Label) : Disjoint ({b} : Set Label) (csub b) := by
  refine Set.disjoint_left.2 (fun t ht h2 => ?_)
  rcases h2 with ⟨j, hj⟩
  rw [Set.mem_singleton_iff] at ht
  subst ht
  have := hj.length_le
  simp at this

lemma disj_children (b : Label) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (sub (b ++ [j])) (sub (b ++ [j'])) := by
  refine Set.disjoint_left.2 (fun t h1 h2 => ?_)
  have hl : (b ++ [j]).length ≤ (b ++ [j']).length := by simp
  have := (List.prefix_of_prefix_length_le h1 h2 hl).eq_of_length (by simp)
  simp at this
  exact h this

lemma X_sg {S : Set Label} {i : Label} (hi : i ∈ S) : Measurable[sg X U S] (X i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ key ⁻¹' S) => fam X U k) (Sum.inl i) hi le_rfl

lemma U_sg {S : Set Label} {i : Label} (k : ℕ) (hi : i ∈ S) : Measurable[sg X U S] (U i k) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ key ⁻¹' S) => fam X U k) (Sum.inr (i, k)) hi le_rfl

lemma fam_le (hgw : GWModel P mk X U ζ c d) (k : Label ⊕ (Label × ℕ)) :
    fam X U k ≤ ‹MeasurableSpace Ω› := by
  cases k with
  | inl i => exact (hgw.measurable_X i).comap_le
  | inr p => exact (hgw.measurable_U p.1 p.2).comap_le

lemma sg_le (hgw : GWModel P mk X U ζ c d) (S : Set Label) : sg X U S ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le (fun k _ => fam_le hgw k)

lemma sg_mono {S T : Set Label} (h : S ⊆ T) : sg X U S ≤ sg X U T :=
  biSup_mono (fun _ hk => h hk)

lemma fam_iIndep (hgw : GWModel P mk X U ζ c d) : iIndep (fam X U) P := by
  have hXi := (iIndepFun_iff_iIndep _ _ _).1 hgw.indep_marks
  have hUi := (iIndepFun_iff_iIndep _ _ _).1 hgw.indep_unif
  have hXU := (IndepFun_iff_Indep _ _ _).1 hgw.indep_marks_unif
  rw [iIndep_iff]
  intro s f hf
  have hL : MeasurableSet[MeasurableSpace.comap (fun ω i => X i ω) inferInstance]
      (⋂ l ∈ s.toLeft, f (Sum.inl l)) := by
    refine Finset.measurableSet_biInter _ (fun l hl => ?_)
    have h1 := hf (Sum.inl l) (Finset.mem_toLeft.1 hl)
    have h2 : Measurable[MeasurableSpace.comap (fun ω i => X i ω) inferInstance] (X l) :=
      fun t ht => ⟨(fun v : Label → M => v l) ⁻¹' t, measurable_pi_apply l ht, rfl⟩
    exact h2.comap_le _ h1
  have hR : MeasurableSet[MeasurableSpace.comap (fun ω (p : Label × ℕ) => U p.1 p.2 ω) inferInstance]
      (⋂ r ∈ s.toRight, f (Sum.inr r)) := by
    refine Finset.measurableSet_biInter _ (fun r hr => ?_)
    have h1 := hf (Sum.inr r) (Finset.mem_toRight.1 hr)
    have h2 : Measurable[MeasurableSpace.comap (fun ω (p : Label × ℕ) => U p.1 p.2 ω)
        inferInstance] (U r.1 r.2) :=
      fun t ht => ⟨(fun v : Label × ℕ → ℝ => v r) ⁻¹' t, measurable_pi_apply r ht, rfl⟩
    exact h2.comap_le _ h1
  have hsplit : ⋂ i ∈ s, f i
      = (⋂ l ∈ s.toLeft, f (Sum.inl l)) ∩ (⋂ r ∈ s.toRight, f (Sum.inr r)) := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_inter_iff, Finset.mem_toLeft, Finset.mem_toRight]
    constructor
    · intro h; exact ⟨fun l hl => h _ hl, fun r hr => h _ hr⟩
    · rintro ⟨h1, h2⟩ i hi
      cases i with
      | inl l => exact h1 l hi
      | inr r => exact h2 r hi
  rw [hsplit, (Indep_iff _ _ _).1 hXU _ _ hL hR, Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight]
  congr 1
  · exact (iIndep_iff _ _).1 hXi s.toLeft (f := fun l => f (Sum.inl l))
      (fun l hl => hf _ (Finset.mem_toLeft.1 hl))
  · exact (iIndep_iff _ _).1 hUi s.toRight (f := fun r => f (Sum.inr r))
      (fun r hr => hf _ (Finset.mem_toRight.1 hr))

lemma indep_sg (hgw : GWModel P mk X U ζ c d) {S T : Set Label} (h : Disjoint S T) :
    Indep (sg X U S) (sg X U T) P :=
  indep_iSup_of_disjoint (fam_le hgw) (fam_iIndep hgw) (h.preimage key)

lemma indepFun_sg (hgw : GWModel P mk X U ζ c d) {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {S T : Set Label} {f : Ω → α} {g : Ω → β}
    (hf : Measurable[sg X U S] f) (hg : Measurable[sg X U T] g) (h : Disjoint S T) :
    IndepFun f g P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_sg hgw h) hf.comap_le)
    hg.comap_le

/-! ## measurability of the tree quantities -/

lemma meas_Wfun (hgw : GWModel P mk X U ζ c d) :
    Measurable (fun p : M × ℝ => d * ζ p.1 p.2
      + mk.Q p.1 * (c - ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j)) :=
  (measurable_const.mul hgw.measurable_ζ).add ((mk.measurable_Q.comp measurable_fst).mul
    (measurable_const.sub (meas_rangeSum _ _ (mk.measurable_N.comp measurable_fst)
      (fun j => (mk.measurable_C j).comp measurable_fst))))

lemma meas_Hs : Measurable (fun p : M × (ℕ → ℝ) =>
    ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j) :=
  meas_rangeSum _ _ (mk.measurable_N.comp measurable_fst)
    (fun j => ((mk.measurable_C j).comp measurable_fst).mul
      ((measurable_pi_apply j).comp measurable_snd))

lemma W_meas_m (hW : Measurable (fun p : M × ℝ => d * ζ p.1 p.2
      + mk.Q p.1 * (c - ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j)))
    {m : MeasurableSpace Ω} {b : Label} {T : ℕ}
    (hX : Measurable[m] (X b)) (hU : Measurable[m] (U b T)) :
    Measurable[m] (W mk X U ζ c d b T) :=
  hW.comp (hX.prodMk hU)

lemma A_meas (hgw : GWModel P mk X U ζ c d) (s : ℕ) :
    ∀ b T, Measurable[sg X U (sub b)] (A mk X U ζ c d b s T) := by
  induction s with
  | zero =>
    intro b T
    have : A mk X U ζ c d b 0 T = W mk X U ζ c d b T := funext (fun ω => A_zero b T ω)
    rw [this]
    exact W_meas_m (meas_Wfun hgw) (X_sg (mem_sub_self b)) (U_sg T (mem_sub_self b))
  | succ s ih =>
    intro b T
    have e : A mk X U ζ c d b (s + 1) T = (fun p : M × (ℕ → ℝ) =>
        ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j) ∘
        (fun ω => (X b ω, fun j => A mk X U ζ c d (b ++ [j]) s T ω)) :=
      funext (fun ω => A_succ b s T ω)
    rw [e]
    have hV : Measurable[sg X U (sub b)] (fun ω j => A mk X U ζ c d (b ++ [j]) s T ω) := by
      let _ := sg X U (sub b)
      exact measurable_pi_lambda _
        (fun j => (ih (b ++ [j]) T).mono (sg_mono (sub_child_subset b j)) le_rfl)
    exact meas_Hs.comp ((X_sg (mem_sub_self b)).prodMk hV)

lemma Rp_meas (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) :
    Measurable[sg X U (sub b)] (Rp mk X U ζ c d b t0) := by
  refine @measurable_of_tendsto_metrizable Ω ℝ (sg X U (sub b)) _ _ _ _
    (fun n ω => ∑ s ∈ Finset.range n, A mk X U ζ c d b s (t0 + s) ω) _ (fun n => ?_) ?_
  · exact Finset.measurable_sum (Finset.range n) (fun s _ => A_meas hgw s b (t0 + s))
  · exact tendsto_pi_nhds.2 (fun ω => (A_summable hgw b t0 ω).hasSum.tendsto_sum_nat)

lemma Rp_meas' (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) :
    Measurable (Rp mk X U ζ c d b t0) :=
  (Rp_meas hgw b t0).mono (sg_le hgw _) le_rfl

/-! ## one-step formulas -/

def Wf (mk : MarkFns M) (ζ : M → ℝ → ℝ) (c d : ℝ) (p : M × ℝ) : ℝ :=
  d * ζ p.1 p.2 + mk.Q p.1 * (c - ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j)

def Hs (mk : MarkFns M) (p : M × (ℕ → ℝ)) : ℝ :=
  ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j

lemma wabs (s : Finset ℕ) (a e : ℕ → ℝ) (c B : ℝ) (ha : ∀ j, 0 ≤ a j)
    (hs : ∑ j ∈ s, a j ≤ c) (hB : 0 ≤ B) (he : ∀ j, |e j| ≤ B) :
    |∑ j ∈ s, a j * e j| ≤ c * B :=
  calc |∑ j ∈ s, a j * e j| ≤ ∑ j ∈ s, |a j * e j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, a j * B := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul, abs_of_nonneg (ha j)]; exact mul_le_mul_of_nonneg_left (he j) (ha j))
    _ = (∑ j ∈ s, a j) * B := by rw [Finset.sum_mul]
    _ ≤ c * B := mul_le_mul_of_nonneg_right hs hB

lemma wsum2_le (hgw : GWModel P mk X U ζ c d) (x : M) :
    ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 ≤ c :=
  le_trans (Finset.sum_le_sum (fun j _ => by
    have h0 := hgw.weights_nonneg x j
    have h1 := hgw.weights_le_one x j
    nlinarith)) (wsum_le hgw x)

lemma abs_int_le [IsProbabilityMeasure P] {f : Ω → ℝ} (B : ℝ) (h : ∀ ω, |f ω| ≤ B) :
    |∫ ω, f ω ∂P| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := B)
    (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using h ω))
  simpa [Real.norm_eq_abs] using this

lemma Z_meas (hgw : GWModel P mk X U ζ c d) (b : Label) (t : ℕ) :
    Measurable (Z X U ζ b t) :=
  hgw.measurable_ζ.comp ((hgw.measurable_X b).prodMk (hgw.measurable_U b t))

lemma Z_bound (hgw : GWModel P mk X U ζ c d) (b : Label) (t : ℕ) (ω : Ω) :
    |Z X U ζ b t ω| ≤ 1 := by
  have hz := hgw.ζ_mem (X b ω) (U b t ω)
  exact abs_le.2 ⟨hz.1, hz.2⟩

lemma wS_meas (hgw : GWModel P mk X U ζ c d) (b : Label) (e : ℕ → ℝ) (k : ℕ) :
    Measurable (fun ω => ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ k * e j) :=
  meas_rangeSum (fun ω => mk.N (X b ω)) (fun j ω => mk.C (X b ω) j ^ k * e j)
    (mk.measurable_N.comp (hgw.measurable_X b))
    (fun j => (((mk.measurable_C j).comp (hgw.measurable_X b)).pow_const k).mul_const _)

lemma wS_bound (hgw : GWModel P mk X U ζ c d) (x : M) (e : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (he : ∀ j, |e j| ≤ B) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    |∑ j ∈ Finset.range (mk.N x), mk.C x j ^ k * e j| ≤ c * B := by
  rcases hk with rfl | rfl
  · exact wabs _ _ _ c B (fun j => by simpa using hgw.weights_nonneg x j)
      (by simpa using wsum_le hgw x) hB he
  · exact wabs _ _ _ c B (fun j => sq_nonneg _) (wsum2_le hgw x) hB he

lemma wS_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (b : Label)
    (e : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (he : ∀ j, |e j| ≤ B) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    Integrable (fun ω => ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ k * e j) P :=
  intg_of_bdd (wS_meas hgw b e k) _ (fun ω => wS_bound hgw _ e B hB he k hk)

lemma Y_meas (b : Label) (t0 : ℕ) :
    Measurable[sg X U {b}] (fun ω => (X b ω, U b t0 ω)) :=
  (X_sg (Set.mem_singleton b)).prodMk (U_sg t0 (Set.mem_singleton b))

lemma V_meas (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) :
    Measurable[sg X U (csub b)] (fun ω j => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω) := by
  have h : ∀ j, Measurable[sg X U (csub b)] (Rp mk X U ζ c d (b ++ [j]) (t0 + 1)) := fun j =>
    (Rp_meas hgw (b ++ [j]) (t0 + 1)).mono (sg_mono (sub_child_csub b j)) le_rfl
  let _ := sg X U (csub b)
  exact measurable_pi_lambda _ h

lemma Rp_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) :
    Integrable (Rp mk X U ζ c d b t0) P :=
  intg_of_bdd (Rp_meas' hgw _ _) _ (fun ω => Rp_bound hgw _ _ ω)

lemma Rp_eqF (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ) :
    Rp mk X U ζ c d b t0 = fun ω => Wf mk ζ c d (X b ω, U b t0 ω)
      + Hs mk (X b ω, fun j => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω) :=
  funext (fun ω => Rp_rec hgw b t0 ω)

lemma Wf_ae (hgw : GWModel P mk X U ζ c d) (b : Label) (t0 : ℕ)
    (hpos : ∀ᵐ ω ∂P, 0 < mk.N (X b ω)) :
    ∀ᵐ ω ∂P, Wf mk ζ c d (X b ω, U b t0 ω) = d * Z X U ζ b t0 ω
      ∧ ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j = c := by
  filter_upwards [hpos] with ω hω
  have h := hgw.weights_sum (X b ω) hω
  refine ⟨?_, h⟩
  simp only [Wf, Z, h, sub_self, mul_zero, add_zero]

lemma mean_formula [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (b : Label)
    (t0 : ℕ) (hpos : ∀ᵐ ω ∂P, 0 < mk.N (X b ω)) :
    ∫ ω, Rp mk X U ζ c d b t0 ω ∂P = d * ∫ ω, Z X U ζ b t0 ω ∂P
      + ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 1
          * ∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P ∂P := by
  set m : ℕ → ℝ := fun j => ∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P with hm
  have hc1 : 0 < 1 - c := by linarith [hgw.c_lt_one]
  have hmB : ∀ j, |m j| ≤ (1 - c)⁻¹ := fun j => abs_int_le _ (fun ω => Rp_bound hgw _ _ ω)
  have hF : Measurable (fun q : (M × ℝ) × (ℕ → ℝ) => Wf mk ζ c d q.1 + Hs mk (q.1.1, q.2)) :=
    ((meas_Wfun hgw).comp measurable_fst).add
      (meas_Hs.comp (measurable_fst.fst.prodMk measurable_snd))
  have hg : Measurable (fun p : M × ℝ => Wf mk ζ c d p
      + ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * m j) :=
    (meas_Wfun hgw).add (meas_rangeSum _ _ (mk.measurable_N.comp measurable_fst)
      (fun j => ((mk.measurable_C j).comp measurable_fst).mul_const _))
  have key := indep_fubini (indepFun_sg hgw (Y_meas b t0) (V_meas hgw b t0) (disj_self_csub b))
    ((Y_meas b t0).mono (sg_le hgw _) le_rfl) ((V_meas hgw b t0).mono (sg_le hgw _) le_rfl)
    hF (by rw [← Rp_eqF hgw b t0]; exact Rp_int hgw b t0) hg (fun p => by
      simp only [Hs]
      rw [integral_add (integrable_const _)
          (integrable_finsetSum _ (fun j _ => (Rp_int hgw _ _).const_mul _)),
        integral_const, integral_finsetSum _ (fun j _ => (Rp_int hgw _ _).const_mul _)]
      simp [integral_const_mul, hm])
  rw [Rp_eqF hgw b t0]
  refine key.trans ?_
  have hZi : Integrable (Z X U ζ b t0) P := intg_of_bdd (Z_meas hgw b t0) 1 (Z_bound hgw b t0)
  have hSi := wS_int hgw b m _ (inv_nonneg.2 hc1.le) hmB 1 (Or.inl rfl)
  rw [← integral_const_mul, ← integral_add (hZi.const_mul d) hSi]
  refine integral_congr_ae ?_
  filter_upwards [Wf_ae hgw b t0 hpos] with ω hω
  rw [hω.1]; simp

lemma var_formula [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (b : Label)
    (t0 : ℕ) (hpos : ∀ᵐ ω ∂P, 0 < mk.N (X b ω)) (μ1 M0 : ℝ)
    (hm : ∀ j, ∫ ω, Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω ∂P = μ1) :
    ∫ ω, (Rp mk X U ζ c d b t0 ω - M0) ^ 2 ∂P
      = ∫ ω, (d * Z X U ζ b t0 ω + c * μ1 - M0) ^ 2 ∂P
      + ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2
          * ∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P ∂P := by
  set v : ℕ → ℝ := fun j => ∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P
    with hv
  have hc1 : 0 < 1 - c := by linarith [hgw.c_lt_one]
  set B := (1 - c)⁻¹ + |μ1| with hBdef
  have hB0 : 0 ≤ B := add_nonneg (inv_nonneg.2 hc1.le) (abs_nonneg _)
  have hDB : ∀ j ω, |Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1| ≤ B := fun j ω =>
    (abs_sub _ _).trans (add_le_add (Rp_bound hgw _ _ ω) le_rfl)
  have hvB : ∀ j, |v j| ≤ B ^ 2 := fun j => abs_int_le _ (fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hDB j ω) 2)
  have hF : Measurable (fun q : (M × ℝ) × (ℕ → ℝ) =>
      (Wf mk ζ c d q.1 + Hs mk (q.1.1, q.2) - M0) ^ 2) :=
    ((((meas_Wfun hgw).comp measurable_fst).add
      (meas_Hs.comp (measurable_fst.fst.prodMk measurable_snd))).sub_const _).pow_const 2
  have hg : Measurable (fun p : M × ℝ =>
      (Wf mk ζ c d p + μ1 * ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j - M0) ^ 2
      + ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j ^ 2 * v j) :=
    ((((meas_Wfun hgw).add (measurable_const.mul (meas_rangeSum _ _
      (mk.measurable_N.comp measurable_fst)
      (fun j => (mk.measurable_C j).comp measurable_fst)))).sub_const _).pow_const 2).add
      (meas_rangeSum _ _ (mk.measurable_N.comp measurable_fst)
        (fun j => (((mk.measurable_C j).comp measurable_fst).pow_const 2).mul_const _))
  have hRint : Integrable (fun ω => (Rp mk X U ζ c d b t0 ω - M0) ^ 2) P :=
    intg_of_bdd (((Rp_meas' hgw b t0).sub_const _).pow_const 2) (((1 - c)⁻¹ + |M0|) ^ 2)
      (fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (Rp_bound hgw _ _ ω) le_rfl)) 2)
  have h0 : ∀ j, ∫ ω, (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1) ∂P = 0 := by
    intro j
    rw [integral_sub (Rp_int hgw _ _) (integrable_const _), integral_const, hm j]
    simp
  have hind : ∀ j j', j ≠ j' → ∫ ω, (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1)
      * (Rp mk X U ζ c d (b ++ [j']) (t0 + 1) ω - μ1) ∂P = 0 := by
    intro j j' hjj
    have hI := indepFun_sg hgw ((Rp_meas hgw (b ++ [j]) (t0 + 1)).sub_const μ1)
      ((Rp_meas hgw (b ++ [j']) (t0 + 1)).sub_const μ1) (disj_children b hjj)
    have := hI.integral_mul_eq_mul_integral
      ((Rp_meas' hgw _ _).sub_const _).aestronglyMeasurable
      ((Rp_meas' hgw _ _).sub_const _).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0 j, zero_mul]
  have key := indep_fubini (indepFun_sg hgw (Y_meas b t0) (V_meas hgw b t0) (disj_self_csub b))
    ((Y_meas b t0).mono (sg_le hgw _) le_rfl) ((V_meas hgw b t0).mono (sg_le hgw _) le_rfl)
    hF (by
      have e : (fun ω => (Wf mk ζ c d (X b ω, U b t0 ω)
          + Hs mk (X b ω, fun j => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω) - M0) ^ 2)
          = fun ω => (Rp mk X U ζ c d b t0 ω - M0) ^ 2 := by
        rw [Rp_eqF hgw b t0]
      exact e ▸ hRint) hg (fun p => by
      dsimp only
      have e : ∀ ω, (Wf mk ζ c d p
            + Hs mk (p.1, fun j => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω) - M0) ^ 2
          = ((Wf mk ζ c d p + μ1 * ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j - M0)
            + ∑ j ∈ Finset.range (mk.N p.1),
                mk.C p.1 j * (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1)) ^ 2 := by
        intro ω
        have : ∑ j ∈ Finset.range (mk.N p.1),
              mk.C p.1 j * (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1)
            = Hs mk (p.1, fun j => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω)
              - μ1 * ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j := by
          simp only [Hs]
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [this]; ring
      refine (integral_congr_ae (ae_of_all _ e)).trans ?_
      refine (sq_expand (Finset.range (mk.N p.1)) _ (fun j => mk.C p.1 j)
        (fun j ω => Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω - μ1) B hB0
        (fun j => (Rp_meas' hgw _ _).sub_const _) hDB h0 hind).trans ?_
      rfl)
  rw [Rp_eqF hgw b t0]
  refine key.trans ?_
  dsimp only
  have hd := hgw.d_pos
  have hA : Integrable (fun ω => (d * Z X U ζ b t0 ω + c * μ1 - M0) ^ 2) P :=
    intg_of_bdd ((((Z_meas hgw b t0).const_mul d).add_const _).sub_const _ |>.pow_const 2)
      ((d + |c * μ1| + |M0|) ^ 2) (fun ω => by
        have h1 : |d * Z X U ζ b t0 ω| ≤ d := by
          rw [abs_mul, abs_of_pos hd]; exact mul_le_of_le_one_right hd.le (Z_bound hgw b t0 ω)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
          (add_le_add ((abs_add_le _ _).trans (add_le_add h1 le_rfl)) le_rfl)) 2)
  have hS2 := wS_int hgw b v (B ^ 2) (sq_nonneg _) hvB 2 (Or.inr rfl)
  rw [← integral_add hA hS2]
  refine integral_congr_ae ?_
  filter_upwards [Wf_ae hgw b t0 hpos] with ω hω
  rw [hω.1, hω.2]
  ring

/-! ## identical distributions -/

lemma XU_indep (hgw : GWModel P mk X U ζ c d) (b : Label) (t : ℕ) : IndepFun (X b) (U b t) P := by
  rw [IndepFun_iff_Indep]
  exact (fam_iIndep hgw).indep (i := Sum.inl b) (j := Sum.inr (b, t)) (by simp)

lemma XU_map [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (b : Label) (t : ℕ) :
    P.map (fun ω => (X b ω, U b t ω))
      = (P.map (X b)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hgw.measurable_X b).aemeasurable
    (hgw.measurable_U b t).aemeasurable).1 (XU_indep hgw b t), (hgw.unif b t).map_eq]

lemma XU_ident [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) {b : Label}
    (hb : b ≠ []) (t : ℕ) :
    IdentDistrib (fun ω => (X b ω, U b t ω)) (fun ω => (X [0] ω, U [0] 0 ω)) P P where
  aemeasurable_fst := ((hgw.measurable_X b).prodMk (hgw.measurable_U b t)).aemeasurable
  aemeasurable_snd := ((hgw.measurable_X [0]).prodMk (hgw.measurable_U [0] 0)).aemeasurable
  map_eq := by rw [XU_map hgw, XU_map hgw, (hgw.ident_marks b hb).map_eq]

lemma XU_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) {b : Label}
    (hb : b ≠ []) (t : ℕ) (φ : M × ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, φ (X b ω, U b t ω) ∂P = ∫ ω, φ (X [0] ω, U [0] 0 ω) ∂P :=
  ((XU_ident hgw hb t).comp hφ).integral_eq

lemma X_int (hgw : GWModel P mk X U ζ c d) {b : Label} (hb : b ≠ []) (φ : M → ℝ)
    (hφ : Measurable φ) : ∫ ω, φ (X b ω) ∂P = ∫ ω, φ (X [0] ω) ∂P :=
  ((hgw.ident_marks b hb).comp hφ).integral_eq

lemma pos_b (hgw : GWModel P mk X U ζ c d) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) {b : Label}
    (hb : b ≠ []) : ∀ᵐ ω ∂P, 0 < mk.N (X b ω) :=
  (hgw.ident_marks b hb).symm.ae_snd (p := fun x => 0 < mk.N x)
    (measurableSet_lt measurable_const mk.measurable_N) hN1

lemma zero_of_le_pow {q K x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ k : ℕ, |x| ≤ q ^ k * K) :
    x = 0 := by
  have ht : Filter.Tendsto (fun k : ℕ => q ^ k * K) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const K
  have : |x| ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall h)
  exact abs_nonpos_iff.1 this

lemma mean_child [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) (b : Label) (hb : b ≠ []) (t0 : ℕ) :
    ∫ ω, Rp mk X U ζ c d b t0 ω ∂P = ∫ ω, Z X U ζ [0] 0 ω ∂P := by
  set μ1 := ∫ ω, Z X U ζ [0] 0 ω ∂P with hμ1
  have hc1 : 0 < 1 - c := by linarith [hgw.c_lt_one]
  have hμ1B : |μ1| ≤ 1 := abs_int_le 1 (Z_bound hgw [0] 0)
  have hU : P.real Set.univ = 1 := by simp
  have claim : ∀ k : ℕ, ∀ b : Label, b ≠ [] → ∀ t0 : ℕ,
      |∫ ω, Rp mk X U ζ c d b t0 ω ∂P - μ1| ≤ c ^ k * ((1 - c)⁻¹ + 1) := by
    intro k
    induction k with
    | zero =>
      intro b _ t0
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add (abs_int_le _ (Rp_bound hgw b t0)) hμ1B)
    | succ k ih =>
      intro b hb t0
      have hpos := pos_b hgw hN1 hb
      rw [mean_formula hgw b t0 hpos]
      have hZ : ∫ ω, Z X U ζ b t0 ω ∂P = μ1 :=
        XU_int hgw hb t0 (fun p => ζ p.1 p.2) hgw.measurable_ζ
      rw [hZ]
      have he : ∀ j, |∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P - μ1|
          ≤ c ^ k * ((1 - c)⁻¹ + 1) :=
        fun j => ih (b ++ [j]) (by simp) (t0 + 1)
      have hK : 0 ≤ c ^ k * ((1 - c)⁻¹ + 1) :=
        mul_nonneg (pow_nonneg hgw.c_nonneg k) (by positivity)
      have e : ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 1
            * ∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P ∂P
          = ∫ ω, (∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 1
            * (∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P - μ1) + c * μ1) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [Wf_ae hgw b t0 hpos] with ω hω
        have h2 := hω.2
        simp only [pow_one, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h2]
        ring
      rw [e, integral_add (wS_int hgw b _ _ hK he 1 (Or.inl rfl)) (integrable_const _),
        integral_const, hU, one_smul]
      set I := ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 1
            * (∫ ω', Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' ∂P - μ1) ∂P with hI
      have hIb : |I| ≤ c * (c ^ k * ((1 - c)⁻¹ + 1)) :=
        abs_int_le _ (fun ω => wS_bound hgw _ _ _ hK he 1 (Or.inl rfl))
      have : d * μ1 + (I + c * μ1) - μ1 = I := by linear_combination μ1 * hcd
      rw [this, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact hIb
  have := zero_of_le_pow hgw.c_nonneg hgw.c_lt_one (fun k => claim k b hb t0)
  linarith

lemma var_child [IsProbabilityMeasure P] (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) (b : Label) (hb : b ≠ []) (t0 : ℕ) :
    ∫ ω, (Rp mk X U ζ c d b t0 ω - ∫ ω, Z X U ζ [0] 0 ω ∂P) ^ 2 ∂P
      = d ^ 2 * (∫ ω, (Z X U ζ [0] 0 ω - ∫ ω, Z X U ζ [0] 0 ω ∂P) ^ 2 ∂P)
        / (1 - rho2 P mk X) := by
  set μ1 := ∫ ω, Z X U ζ [0] 0 ω ∂P with hμ1
  set VZ := ∫ ω, (Z X U ζ [0] 0 ω - μ1) ^ 2 ∂P with hVZ
  set ρ := rho2 P mk X with hρ
  have hρc : ρ ≤ c := by
    have := abs_int_le (P := P)
      (f := fun ω => ∑ j ∈ Finset.range (mk.N (X [0] ω)), mk.C (X [0] ω) j ^ 2) c
      (fun ω => by
        rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
        exact wsum2_le hgw _)
    exact (le_abs_self _).trans this
  have hρ1 : 0 < 1 - ρ := by linarith [hgw.c_lt_one]
  set vs := d ^ 2 * VZ / (1 - ρ) with hvs
  have hfix : vs = d ^ 2 * VZ + ρ * vs := by
    rw [hvs]; field_simp; ring
  have hc1 : 0 < 1 - c := by linarith [hgw.c_lt_one]
  have hU : P.real Set.univ = 1 := by simp
  set K := ((1 - c)⁻¹ + |μ1|) ^ 2 + |vs| with hKdef
  have hK : 0 ≤ K := by positivity
  have hφρ : Measurable (fun x : M => ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 * vs) :=
    meas_rangeSum _ _ mk.measurable_N (fun j => ((mk.measurable_C j).pow_const 2).mul_const _)
  have claim : ∀ k : ℕ, ∀ b : Label, b ≠ [] → ∀ t0 : ℕ,
      |∫ ω, (Rp mk X U ζ c d b t0 ω - μ1) ^ 2 ∂P - vs| ≤ c ^ k * K := by
    intro k
    induction k with
    | zero =>
      intro b _ t0
      rw [pow_zero, one_mul]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      exact abs_int_le _ (fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (Rp_bound hgw _ _ ω) le_rfl)) 2)
    | succ k ih =>
      intro b hb t0
      have hpos := pos_b hgw hN1 hb
      rw [var_formula hgw b t0 hpos μ1 μ1
        (fun j => mean_child hgw hcd hN1 (b ++ [j]) (by simp) (t0 + 1))]
      have hA : ∫ ω, (d * Z X U ζ b t0 ω + c * μ1 - μ1) ^ 2 ∂P = d ^ 2 * VZ := by
        refine (XU_int hgw hb t0 (fun p => (d * ζ p.1 p.2 + c * μ1 - μ1) ^ 2)
          (((hgw.measurable_ζ.const_mul d).add_const _).sub_const _ |>.pow_const 2)).trans ?_
        rw [hVZ, ← integral_const_mul (d ^ 2)]
        congr 1
        funext ω
        have : c = 1 - d := by linarith
        simp only [Z]
        rw [this]
        ring
      have he : ∀ j, |∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P - vs|
          ≤ c ^ k * K := fun j => ih (b ++ [j]) (by simp) (t0 + 1)
      have hK' : 0 ≤ c ^ k * K := mul_nonneg (pow_nonneg hgw.c_nonneg k) hK
      have e : ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2
            * ∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P ∂P
          = ∫ ω, (∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2
            * (∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P - vs)
            + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2 * vs) ∂P :=
        integral_congr_ae (ae_of_all _ (fun ω => by
          beta_reduce
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)))
      have hvsB : ∀ j : ℕ, |(fun _ : ℕ => vs) j| ≤ |vs| := fun j => le_rfl
      rw [hA, e, integral_add (wS_int hgw b _ _ hK' he 2 (Or.inr rfl))
        (wS_int hgw b (fun _ => vs) |vs| (abs_nonneg _) hvsB 2 (Or.inr rfl))]
      have hρb : ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2 * vs ∂P
          = ρ * vs := by
        rw [X_int hgw hb (fun x => ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 * vs) hφρ]
        simp only [← Finset.sum_mul]
        rw [integral_mul_const]
        rfl
      rw [hρb]
      set I := ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2
            * (∫ ω', (Rp mk X U ζ c d (b ++ [j]) (t0 + 1) ω' - μ1) ^ 2 ∂P - vs) ∂P with hI
      have hIb : |I| ≤ c * (c ^ k * K) :=
        abs_int_le _ (fun ω => wS_bound hgw _ _ _ hK' he 2 (Or.inr rfl))
      have : d ^ 2 * VZ + (I + ρ * vs) - vs = I := by linarith [hfix]
      rw [this, pow_succ, mul_comm (c ^ k) c, mul_assoc]
      exact hIb
  have := zero_of_le_pow hgw.c_nonneg hgw.c_lt_one (fun k => claim k b hb t0)
  linarith

end model

end P03a

open MeasureTheory ProbabilityTheory DirectedOpinion.NoMemory in
theorem solution {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : MarkFns M) (X : Label → Ω → M)
    (U : Label → ℕ → Ω → ℝ) (ζ : M → ℝ → ℝ) (c d : ℝ)
    (hgw : GWModel P mk X U ζ c d) (hcd : c + d = 1)
    (hN0 : ∀ᵐ ω ∂P, 0 < mk.N (X [] ω)) (hN1 : ∀ᵐ ω ∂P, 0 < mk.N (X [0] ω)) :
    (∫ ω, Rstar mk X U ζ c d ω ∂P =
      d * ∫ ω, Z X U ζ [] 0 ω ∂P + c * ∫ ω, Z X U ζ [0] 0 ω ∂P) ∧
    variance (Rstar mk X U ζ c d) P =
      d ^ 2 * variance (Z X U ζ [] 0) P +
        rho2Star P mk X * d ^ 2 / (1 - rho2 P mk X) * variance (Z X U ζ [0] 0) P := by
  have hRs : Rstar mk X U ζ c d = P03a.Rp mk X U ζ c d [] 0 := funext (P03a.Rstar_eq hcd)
  have hU : P.real Set.univ = 1 := by simp
  have hmean : ∫ ω, P03a.Rp mk X U ζ c d [] 0 ω ∂P
      = d * ∫ ω, Z X U ζ [] 0 ω ∂P + c * ∫ ω, Z X U ζ [0] 0 ω ∂P := by
    rw [P03a.mean_formula hgw [] 0 hN0]
    congr 1
    have e : ∀ ω, ∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j ^ 1
        * ∫ ω', P03a.Rp mk X U ζ c d ([] ++ [j]) (0 + 1) ω' ∂P
        = (∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j) * ∫ ω, Z X U ζ [0] 0 ω ∂P :=
      fun ω => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by
          rw [pow_one, P03a.mean_child hgw hcd hN1 _ (by simp) _])
    rw [show c * ∫ ω, Z X U ζ [0] 0 ω ∂P = ∫ _ω, c * ∫ ω, Z X U ζ [0] 0 ω ∂P ∂P by
      rw [integral_const, hU, one_smul]]
    refine integral_congr_ae ?_
    filter_upwards [P03a.Wf_ae hgw [] 0 hN0] with ω hω
    rw [e ω, hω.2]
  have hvar : ∫ ω, (P03a.Rp mk X U ζ c d [] 0 ω
        - (d * ∫ ω, Z X U ζ [] 0 ω ∂P + c * ∫ ω, Z X U ζ [0] 0 ω ∂P)) ^ 2 ∂P
      = d ^ 2 * ∫ ω, (Z X U ζ [] 0 ω - ∫ ω, Z X U ζ [] 0 ω ∂P) ^ 2 ∂P
        + rho2Star P mk X * (d ^ 2 * (∫ ω, (Z X U ζ [0] 0 ω - ∫ ω, Z X U ζ [0] 0 ω ∂P) ^ 2 ∂P)
          / (1 - rho2 P mk X)) := by
    rw [P03a.var_formula hgw [] 0 hN0 (∫ ω, Z X U ζ [0] 0 ω ∂P) _
      (fun j => P03a.mean_child hgw hcd hN1 _ (by simp) _)]
    congr 1
    · rw [← integral_const_mul (d ^ 2)]
      exact integral_congr_ae (ae_of_all _ (fun ω => by ring))
    · have e : ∀ ω, ∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j ^ 2
          * ∫ ω', (P03a.Rp mk X U ζ c d ([] ++ [j]) (0 + 1) ω'
              - ∫ ω, Z X U ζ [0] 0 ω ∂P) ^ 2 ∂P
          = (∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j ^ 2)
            * (d ^ 2 * (∫ ω, (Z X U ζ [0] 0 ω - ∫ ω, Z X U ζ [0] 0 ω ∂P) ^ 2 ∂P)
              / (1 - rho2 P mk X)) := fun ω => by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by
          rw [P03a.var_child hgw hcd hN1 _ (by simp) _])
      rw [integral_congr_ae (ae_of_all _ e), integral_mul_const]
      rfl
  have hRm : Measurable (Rstar mk X U ζ c d) := hRs ▸ P03a.Rp_meas' hgw [] 0
  refine ⟨by rw [hRs, hmean], ?_⟩
  rw [variance_eq_integral hRm.aemeasurable, variance_eq_integral
    (P03a.Z_meas hgw [] 0).aemeasurable, variance_eq_integral (P03a.Z_meas hgw [0] 0).aemeasurable,
    hRs, hmean, hvar]
  ring
