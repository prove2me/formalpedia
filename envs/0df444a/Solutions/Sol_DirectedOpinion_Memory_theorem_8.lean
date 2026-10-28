-- Prove2me | solution 1 for DirectedOpinion.Memory.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T09:36:33.583565+00:00
-- url     : https://prove2.me/submissions/64f4dd36-20f7-4d31-88c3-e6ec2a57d9b4

import Mathlib
import Definitions.Def_DirectedOpinion_Memory_Setting
open MeasureTheory ProbabilityTheory

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace T8
open DirectedOpinion.NoMemory DirectedOpinion.Memory

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

lemma abs_int_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (B : ℝ) (h : ∀ ω, |f ω| ≤ B) : |∫ ω, f ω ∂P| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := B)
    (ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using h ω))
  simpa [Real.norm_eq_abs] using this

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

/-- integral of a random-range sum = tsum of the integrals of the truncated terms. -/
lemma int_rangeSum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (N : Ω → ℕ) (h : ℕ → Ω → ℝ) (a : ℕ → Ω → ℝ) (K : ℝ) (hN : Measurable N)
    (hh : ∀ j, Measurable (h j)) (ha : ∀ j, Measurable (a j)) (hha : ∀ j ω, |h j ω| ≤ a j ω)
    (hK : ∀ ω, ∑ j ∈ Finset.range (N ω), a j ω ≤ K) :
    ∫ ω, ∑ j ∈ Finset.range (N ω), h j ω ∂P
      = ∑' j, ∫ ω, (if j < N ω then h j ω else 0) ∂P := by
  set F : ℕ → Ω → ℝ := fun j ω => if j < N ω then h j ω else 0 with hFdef
  have ha0 : ∀ j ω, 0 ≤ a j ω := fun j ω => (abs_nonneg _).trans (hha j ω)
  have e : ∀ ω, ∑ j ∈ Finset.range (N ω), h j ω = ∑' j, F j ω := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (N ω)) (fun j hj => by
      simp only [Finset.mem_range] at hj; simp [hFdef, hj])]
    exact Finset.sum_congr rfl (fun j hj => by
      simp only [Finset.mem_range] at hj; simp [hFdef, hj])
  have hFm : ∀ j, Measurable (F j) := fun j =>
    Measurable.ite (measurableSet_lt measurable_const hN) (hh j) measurable_const
  have hFb : ∀ J : Finset ℕ, ∀ ω, ∑ j ∈ J, |F j ω| ≤ K := by
    intro J ω
    calc ∑ j ∈ J, |F j ω| ≤ ∑ j ∈ J.filter (fun j => j < N ω), a j ω := by
          rw [Finset.sum_filter]
          exact Finset.sum_le_sum (fun j _ => by
            by_cases hj : j < N ω
            · simp [hFdef, hj, hha j ω]
            · simp [hFdef, hj])
      _ ≤ ∑ j ∈ Finset.range (N ω), a j ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
            simp only [Finset.mem_filter] at hj; simpa using hj.2) (fun j _ _ => ha0 j ω)
      _ ≤ K := hK ω
  have hFint : ∀ j, Integrable (F j) P := fun j =>
    intg_of_bdd (hFm j) K (fun ω => by simpa using hFb {j} ω)
  have hsum : Summable (fun j => ∫ ω, ‖F j ω‖ ∂P) := by
    refine summable_of_sum_le (c := K) (fun j => integral_nonneg (fun ω => norm_nonneg _))
      (fun J => ?_)
    rw [← integral_finsetSum _ (fun j _ => (hFint j).norm)]
    have : ∫ ω, ∑ j ∈ J, ‖F j ω‖ ∂P ≤ ∫ _ω, K ∂P :=
      integral_mono (integrable_finsetSum _ (fun j _ => (hFint j).norm)) (integrable_const _)
        (fun ω => by simpa [Real.norm_eq_abs] using hFb J ω)
    simpa using this
  rw [integral_congr_ae (ae_of_all _ e)]
  exact (integral_tsum_of_summable_integral_norm hFint hsum).symm

lemma int_rangeSum_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (N : Ω → ℕ) (h : ℕ → Ω → ℝ) (a : ℕ → Ω → ℝ) (K : ℝ) (hN : Measurable N)
    (hh : ∀ j, Measurable (h j)) (ha : ∀ j, Measurable (a j)) (hha : ∀ j ω, |h j ω| ≤ a j ω)
    (hK : ∀ ω, ∑ j ∈ Finset.range (N ω), a j ω ≤ K)
    (h0 : ∀ j, ∫ ω, (if j < N ω then h j ω else 0) ∂P = 0) :
    ∫ ω, ∑ j ∈ Finset.range (N ω), h j ω ∂P = 0 := by
  rw [int_rangeSum N h a K hN hh ha hha hK]
  simp [h0]

/-! ## Deterministic tree lemmas -/

lemma treeOp_zero_succ (n : Label → ℕ) (w : Label → ℕ → ℝ) (f : Label → ℝ) (s : ℕ)
    (i : Label) :
    (treeOp n w 0)^[s+1] f i
      = ∑ j ∈ Finset.range (n i), w i j * (treeOp n w 0)^[s] f (i ++ [j]) := by
  rw [Function.iterate_succ_apply']; simp [treeOp]

lemma wabs (s : Finset ℕ) (a e : ℕ → ℝ) (c B : ℝ) (ha : ∀ j, 0 ≤ a j)
    (hs : ∑ j ∈ s, a j ≤ c) (hB : 0 ≤ B) (he : ∀ j, |e j| ≤ B) :
    |∑ j ∈ s, a j * e j| ≤ c * B :=
  calc |∑ j ∈ s, a j * e j| ≤ ∑ j ∈ s, |a j * e j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, a j * B := Finset.sum_le_sum (fun j _ => by
        rw [abs_mul, abs_of_nonneg (ha j)]; exact mul_le_mul_of_nonneg_left (he j) (ha j))
    _ = (∑ j ∈ s, a j) * B := by rw [Finset.sum_mul]
    _ ≤ c * B := mul_le_mul_of_nonneg_right hs hB

lemma treeOp_iter_bound (n : Label → ℕ) (w : Label → ℕ → ℝ) (c lam : ℝ) (hlam : 0 ≤ lam)
    (hw0 : ∀ i j, 0 ≤ w i j) (hws : ∀ i, ∑ j ∈ Finset.range (n i), w i j ≤ c) (s : ℕ) :
    ∀ (f : Label → ℝ) (B : ℝ), (∀ i, |f i| ≤ B) →
      ∀ i, |(treeOp n w lam)^[s] f i| ≤ (c + lam) ^ s * B := by
  induction s with
  | zero => intro f B hf i; simpa using hf i
  | succ s ih =>
    intro f B hf i
    rw [Function.iterate_succ_apply]
    have h1 : ∀ i, |treeOp n w lam f i| ≤ (c + lam) * B := by
      intro i
      have hB : 0 ≤ B := le_trans (abs_nonneg _) (hf i)
      simp only [treeOp]
      calc |∑ j ∈ Finset.range (n i), w i j * f (i ++ [j]) + lam * f i|
          ≤ |∑ j ∈ Finset.range (n i), w i j * f (i ++ [j])| + |lam * f i| := abs_add_le _ _
        _ ≤ c * B + lam * B := by
            gcongr
            · exact wabs _ _ _ c B (hw0 i) (hws i) hB (fun j => hf _)
            · rw [abs_mul, abs_of_nonneg hlam]; exact mul_le_mul_of_nonneg_left (hf i) hlam
        _ = (c + lam) * B := by ring
    have := ih (treeOp n w lam f) ((c + lam) * B) h1 i
    rw [pow_succ, mul_assoc]; exact this

lemma iter_add (n : Label → ℕ) (w : Label → ℕ → ℝ) (lam : ℝ) (s : ℕ) :
    ∀ f h : Label → ℝ, (treeOp n w lam)^[s] (fun i => f i + h i)
      = fun i => (treeOp n w lam)^[s] f i + (treeOp n w lam)^[s] h i := by
  induction s with
  | zero => intro f h; rfl
  | succ s ih =>
    intro f h
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih]
    funext i
    simp only [treeOp, mul_add, Finset.sum_add_distrib]
    ring

lemma pascal (s : ℕ) (lam : ℝ) (x : ℕ → ℝ) :
    ∑ l ∈ Finset.range (s + 1), ((s.choose l : ℝ) * lam ^ (s - l)) * x (l + 1)
      + lam * ∑ l ∈ Finset.range (s + 1), ((s.choose l : ℝ) * lam ^ (s - l)) * x l
    = ∑ l ∈ Finset.range (s + 2), (((s + 1).choose l : ℝ) * lam ^ (s + 1 - l)) * x l := by
  rw [Finset.sum_range_succ' _ (s + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.add_sub_add_right, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [Finset.mul_sum, Finset.sum_range_succ' (fun l => lam * (((s.choose l : ℝ)) *
    lam ^ (s - l) * x l))]
  rw [Finset.sum_range_succ (fun l => (s.choose (l + 1) : ℝ) * lam ^ (s - l) * x (l + 1))]
  simp only [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero]
  have : ∑ l ∈ Finset.range s, (s.choose (l + 1) : ℝ) * lam ^ (s - l) * x (l + 1)
      = ∑ l ∈ Finset.range s, lam * ((s.choose (l + 1) : ℝ) * lam ^ (s - (l + 1)) * x (l + 1)) := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    simp only [Finset.mem_range] at hl
    have e : s - l = (s - (l + 1)) + 1 := by omega
    rw [e, pow_succ]; ring
  rw [this, pow_succ]; ring

lemma iter_binom (n : Label → ℕ) (w : Label → ℕ → ℝ) (lam : ℝ) (s : ℕ) :
    ∀ (f : Label → ℝ) (i : Label), (treeOp n w lam)^[s] f i
      = ∑ l ∈ Finset.range (s + 1), ((s.choose l : ℝ) * lam ^ (s - l))
          * (treeOp n w 0)^[l] f i := by
  induction s with
  | zero => intro f i; simp
  | succ s ih =>
    intro f i
    rw [Function.iterate_succ_apply']
    show ∑ j ∈ Finset.range (n i), w i j * (treeOp n w lam)^[s] f (i ++ [j])
      + lam * (treeOp n w lam)^[s] f i = _
    simp_rw [ih]
    rw [← pascal s lam (fun l => (treeOp n w 0)^[l] f i)]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [treeOp_zero_succ, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## The model -/

section model
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]

/-- E[ξ(x, U)] for U uniform on [0,1]. -/
noncomputable def gf (ξ : M → ℝ → ℝ) (x : M) : ℝ :=
  ∫ u, ξ x u ∂(volume.restrict (Set.Icc (0 : ℝ) 1))

/-- noise 𝓦_b^(k) - 𝓨_b. -/
noncomputable def Dn (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ) (ξ : M → ℝ → ℝ)
    (b : Label) (k : ℕ) (ω : Ω) : ℝ :=
  Z X U ξ b k ω - gf ξ (X b ω)

noncomputable def Ql (mk : MarkFns M) (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ)
    (ξ : M → ℝ → ℝ) (b : Label) (l k : ℕ) (ω : Ω) : ℝ :=
  (treeOp (nAt mk X ω) (wAt mk X ω) 0)^[l] (fun i => Dn X U ξ i k ω) b

noncomputable def Ry (mk : MarkFns M) (X : Label → Ω → M) (ξ : M → ℝ → ℝ) (c d : ℝ)
    (b : Label) (ω : Ω) : ℝ :=
  ∑' s, (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => gf ξ (X i ω)) b

noncomputable def Gs (mk : MarkFns M) (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ)
    (ξ : M → ℝ → ℝ) (c d : ℝ) (b : Label) (s : ℕ) (ω : Ω) : ℝ :=
  (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => Dn X U ξ i s ω) b

noncomputable def Nz (mk : MarkFns M) (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ)
    (ξ : M → ℝ → ℝ) (c d : ℝ) (b : Label) (ω : Ω) : ℝ :=
  ∑' s, Gs mk X U ξ c d b s ω

variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

lemma wsum_le (hgw : GWModel P mk X U ξ c d) (x : M) :
    ∑ j ∈ Finset.range (mk.N x), mk.C x j ≤ c := by
  rcases Nat.eq_zero_or_pos (mk.N x) with h | h
  · simp [h, hgw.c_nonneg]
  · exact (hgw.weights_sum x h).le

lemma wsum_nonneg (hgw : GWModel P mk X U ξ c d) (x : M) :
    0 ≤ ∑ j ∈ Finset.range (mk.N x), mk.C x j :=
  Finset.sum_nonneg (fun j _ => hgw.weights_nonneg x j)

lemma nu_prob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; simp⟩

omit [MeasurableSpace Ω] in
lemma gf_meas' (hξ : Measurable (Function.uncurry ξ)) : Measurable (gf ξ) :=
  (hξ.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Icc (0 : ℝ) 1))).measurable

lemma gf_meas (hgw : GWModel P mk X U ξ c d) : Measurable (gf ξ) :=
  (hgw.measurable_ζ.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Icc (0 : ℝ) 1))).measurable

lemma gf_bound (hgw : GWModel P mk X U ξ c d) (x : M) : |gf ξ x| ≤ 1 := by
  have := (nu_prob : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)))
  exact abs_int_le 1 (fun u => abs_le.2 ⟨(hgw.ζ_mem x u).1, (hgw.ζ_mem x u).2⟩)

lemma Z_meas (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ) :
    Measurable (Z X U ξ b t) :=
  hgw.measurable_ζ.comp ((hgw.measurable_X b).prodMk (hgw.measurable_U b t))

lemma Z_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ) (ω : Ω) :
    |Z X U ξ b t ω| ≤ 1 := by
  have hz := hgw.ζ_mem (X b ω) (U b t ω)
  exact abs_le.2 ⟨hz.1, hz.2⟩

lemma Dn_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ) (ω : Ω) :
    |Dn X U ξ b t ω| ≤ 2 := by
  unfold Dn
  have := (abs_sub _ _).trans (add_le_add (Z_bound hgw b t ω) (gf_bound hgw (X b ω)))
  linarith

lemma int_U (hgw : GWModel P mk X U ξ c d) (b : Label) (k : ℕ) (x : M) :
    ∫ ω, ξ x (U b k ω) ∂P = gf ξ x := by
  have hm : Measurable (fun u => ξ x u) := hgw.measurable_ζ.comp measurable_prodMk_left
  rw [← integral_map (hgw.measurable_U b k).aemeasurable hm.aestronglyMeasurable,
    (hgw.unif b k).map_eq]
  rfl

lemma Ql_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (l k : ℕ) (ω : Ω) :
    |Ql mk X U ξ b l k ω| ≤ c ^ l * 2 := by
  have := treeOp_iter_bound (nAt mk X ω) (wAt mk X ω) c 0 le_rfl
    (fun i j => hgw.weights_nonneg _ j) (fun i => wsum_le hgw _) l
    (fun i => Dn X U ξ i k ω) 2 (fun i => Dn_bound hgw i k ω) b
  simpa [Ql] using this

lemma Ql_zero (b : Label) (k : ℕ) (ω : Ω) : Ql mk X U ξ b 0 k ω = Dn X U ξ b k ω := by
  simp [Ql]

lemma Ql_succ (b : Label) (l k : ℕ) (ω : Ω) :
    Ql mk X U ξ b (l + 1) k ω = ∑ j ∈ Finset.range (mk.N (X b ω)),
      mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω := by
  unfold Ql; rw [treeOp_zero_succ]; rfl

lemma Del_bound (hgw : GWModel P mk X U ξ c d) (f : Label → ℝ) (B : ℝ) (hf : ∀ i, |f i| ≤ B)
    (s : ℕ) (b : Label) (ω : Ω) :
    |(treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] f b| ≤ (1 - d) ^ s * B := by
  have hlam : 0 ≤ 1 - c - d := by linarith [hgw.cd_le_one]
  have := treeOp_iter_bound (nAt mk X ω) (wAt mk X ω) c (1 - c - d) hlam
    (fun i j => hgw.weights_nonneg _ j) (fun i => wsum_le hgw _) s f B hf b
  rwa [show c + (1 - c - d) = 1 - d by ring] at this

lemma one_sub_d (hgw : GWModel P mk X U ξ c d) : 0 ≤ 1 - d ∧ 1 - d < 1 :=
  ⟨by linarith [hgw.d_le_one], by linarith [hgw.d_pos]⟩

lemma Gs_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (s : ℕ) (ω : Ω) :
    |Gs mk X U ξ c d b s ω| ≤ (1 - d) ^ s * 2 :=
  Del_bound hgw _ 2 (fun i => Dn_bound hgw i s ω) s b ω

lemma Gs_summable (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    Summable (fun s => Gs mk X U ξ c d b s ω) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (one_sub_d hgw).1
    (one_sub_d hgw).2).mul_right 2)
    (fun s => by rw [Real.norm_eq_abs]; exact Gs_bound hgw b s ω)

lemma Ry_summable (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    Summable (fun s => (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s]
      (fun i => gf ξ (X i ω)) b) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (one_sub_d hgw).1
    (one_sub_d hgw).2).mul_right 1)
    (fun s => by
      rw [Real.norm_eq_abs]
      exact Del_bound hgw _ 1 (fun i => gf_bound hgw _) s b ω)

lemma lim_split (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    limOpinion mk X (Z X U ξ) c d b ω = Ry mk X ξ c d b ω + Nz mk X U ξ c d b ω := by
  unfold limOpinion nodeOpinion Ry Nz Gs
  have e : ∀ s, (fun j => Z X U ξ j s ω) = fun j => gf ξ (X j ω) + Dn X U ξ j s ω := by
    intro s; funext j; simp [Dn]
  simp_rw [e, iter_add]
  exact (Ry_summable hgw b ω).tsum_add (Gs_summable hgw b ω)

lemma Ry_rec (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    (c + d) * Ry mk X ξ c d b ω = gf ξ (X b ω)
      + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * Ry mk X ξ c d (b ++ [j]) ω := by
  have key : Ry mk X ξ c d b ω = gf ξ (X b ω)
      + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * Ry mk X ξ c d (b ++ [j]) ω
      + (1 - c - d) * Ry mk X ξ c d b ω := by
    conv_lhs => unfold Ry; rw [(Ry_summable hgw b ω).tsum_eq_zero_add]
    simp only [Function.iterate_zero, id]
    rw [add_assoc]
    congr 1
    have e : ∀ s, (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s + 1]
        (fun i => gf ξ (X i ω)) b
        = ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j *
            (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => gf ξ (X i ω)) (b ++ [j])
          + (1 - c - d) *
            (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => gf ξ (X i ω)) b := by
      intro s; rw [Function.iterate_succ_apply']; rfl
    simp_rw [e]
    rw [Summable.tsum_add (summable_sum (fun j _ => (Ry_summable hgw (b ++ [j]) ω).mul_left _))
      ((Ry_summable hgw b ω).mul_left _),
      Summable.tsum_finsetSum (fun j _ => (Ry_summable hgw (b ++ [j]) ω).mul_left _),
      tsum_mul_left]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [tsum_mul_left]; rfl)
  linarith

end model

/-! ## sigma-algebras -/

section sig
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

abbrev Key := Label ⊕ (Label × ℕ)

def fam (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ) : Key → MeasurableSpace Ω
  | Sum.inl i => MeasurableSpace.comap (X i) inferInstance
  | Sum.inr p => MeasurableSpace.comap (U p.1 p.2) inferInstance

def sgK (X : Label → Ω → M) (U : Label → ℕ → Ω → ℝ) (K : Set Key) : MeasurableSpace Ω :=
  ⨆ e ∈ K, fam X U e

def Ksub (b : Label) (l k : ℕ) : Set Key :=
  {e | (∃ u, e = Sum.inl u ∧ b <+: u) ∨ ∃ t : Label, t.length = l ∧ e = Sum.inr (b ++ t, k)}

def Kc (T : Set Label) (k : ℕ) : Set Key := {e | ∀ u ∈ T, e ≠ Sum.inr (u, k)}

lemma fam_le (hgw : GWModel P mk X U ξ c d) (e : Key) : fam X U e ≤ ‹MeasurableSpace Ω› := by
  cases e with
  | inl i => exact (hgw.measurable_X i).comap_le
  | inr p => exact (hgw.measurable_U p.1 p.2).comap_le

lemma sgK_le (hgw : GWModel P mk X U ξ c d) (K : Set Key) : sgK X U K ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le (fun e _ => fam_le hgw e)

lemma sgK_mono {K K' : Set Key} (h : K ⊆ K') : sgK X U K ≤ sgK X U K' :=
  biSup_mono (fun _ hk => h hk)

lemma X_sgK {K : Set Key} {i : Label} (h : Sum.inl i ∈ K) : Measurable[sgK X U K] (X i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun e (_ : e ∈ K) => fam X U e) (Sum.inl i) h le_rfl

lemma U_sgK {K : Set Key} {i : Label} {k : ℕ} (h : Sum.inr (i, k) ∈ K) :
    Measurable[sgK X U K] (U i k) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun e (_ : e ∈ K) => fam X U e) (Sum.inr (i, k)) h le_rfl

lemma fam_iIndep (hgw : GWModel P mk X U ξ c d) : iIndep (fam X U) P := by
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

lemma indep_sgK (hgw : GWModel P mk X U ξ c d) {K K' : Set Key} (h : Disjoint K K') :
    Indep (sgK X U K) (sgK X U K') P :=
  indep_iSup_of_disjoint (fam_le hgw) (fam_iIndep hgw) h

lemma indepFun_sgK (hgw : GWModel P mk X U ξ c d) {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {K K' : Set Key} {f : Ω → α} {g : Ω → β}
    (hf : Measurable[sgK X U K] f) (hg : Measurable[sgK X U K'] g) (h : Disjoint K K') :
    IndepFun f g P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_sgK hgw h) hf.comap_le)
    hg.comap_le

lemma meas_Hs : Measurable (fun p : M × (ℕ → ℝ) =>
    ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j) :=
  meas_rangeSum _ _ (mk.measurable_N.comp measurable_fst)
    (fun j => ((mk.measurable_C j).comp measurable_fst).mul
      ((measurable_pi_apply j).comp measurable_snd))

omit [MeasurableSpace Ω] in
lemma Dn_meas_m (hξ : Measurable (Function.uncurry ξ)) {m : MeasurableSpace Ω} {b : Label}
    {k : ℕ} (hX : Measurable[m] (X b)) (hU : Measurable[m] (U b k)) :
    Measurable[m] (Dn X U ξ b k) := by
  have hF : Measurable (fun p : M × ℝ => ξ p.1 p.2 - gf ξ p.1) :=
    hξ.sub ((gf_meas' hξ).comp measurable_fst)
  exact hF.comp (hX.prodMk hU)

lemma Ksub_child (b : Label) (j l k : ℕ) : Ksub (b ++ [j]) l k ⊆ Ksub b (l + 1) k := by
  rintro e (⟨u, rfl, hu⟩ | ⟨t, ht, rfl⟩)
  · exact Or.inl ⟨u, rfl, (List.prefix_append b [j]).trans hu⟩
  · exact Or.inr ⟨[j] ++ t, by simp [ht], by simp⟩

lemma inl_Ksub (b : Label) (l k : ℕ) : (Sum.inl b : Key) ∈ Ksub b l k :=
  Or.inl ⟨b, rfl, List.prefix_refl b⟩

set_option maxHeartbeats 1000000 in
lemma Ql_meas (hgw : GWModel P mk X U ξ c d) (k l : ℕ) :
    ∀ b, Measurable[sgK X U (Ksub b l k)] (Ql mk X U ξ b l k) := by
  induction l with
  | zero =>
    intro b
    have : Ql mk X U ξ b 0 k = Dn X U ξ b k := funext (fun ω => Ql_zero b k ω)
    rw [this]
    exact Dn_meas_m hgw.measurable_ζ (X_sgK (inl_Ksub b 0 k)) (U_sgK (Or.inr ⟨[], rfl, by simp⟩))
  | succ l ih =>
    intro b
    have e : Ql mk X U ξ b (l + 1) k = (fun p : M × (ℕ → ℝ) =>
        ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j) ∘
        (fun ω => (X b ω, fun j => Ql mk X U ξ (b ++ [j]) l k ω)) :=
      funext (fun ω => Ql_succ b l k ω)
    rw [e]
    have hV : Measurable[sgK X U (Ksub b (l + 1) k)]
        (fun ω j => Ql mk X U ξ (b ++ [j]) l k ω) := by
      let _ := sgK X U (Ksub b (l + 1) k)
      exact measurable_pi_lambda _
        (fun j => (ih (b ++ [j])).mono (sgK_mono (Ksub_child b j l k)) le_rfl)
    exact meas_Hs.comp ((X_sgK (inl_Ksub b (l + 1) k)).prodMk hV)

lemma Ql_meas' (hgw : GWModel P mk X U ξ c d) (b : Label) (l k : ℕ) :
    Measurable (Ql mk X U ξ b l k) :=
  (Ql_meas hgw k l b).mono (sgK_le hgw _) le_rfl

lemma Ksub_Kc {b : Label} {l' k' : ℕ} {T : Set Label} {k : ℕ}
    (h : ∀ t : Label, t.length = l' → k' = k → b ++ t ∉ T) : Ksub b l' k' ⊆ Kc T k := by
  rintro e (⟨u, rfl, _⟩ | ⟨t, ht, rfl⟩) v hv
  · simp
  · intro heq
    simp only [Sum.inr.injEq, Prod.mk.injEq] at heq
    exact h t ht heq.2 (heq.1 ▸ hv)

lemma inl_Kc (T : Set Label) (k : ℕ) (i : Label) : (Sum.inl i : Key) ∈ Kc T k :=
  fun _ _ => by simp

set_option maxHeartbeats 1000000 in
/-- Orthogonality of the noise layers. -/
lemma orth [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (k : ℕ) (T : Set Label)
    (l : ℕ) : ∀ (b : Label) (Ψ : Ω → ℝ) (B : ℝ), Measurable[sgK X U (Kc T k)] Ψ →
      (∀ ω, |Ψ ω| ≤ B) → (∀ t : Label, t.length = l → b ++ t ∈ T) →
      ∫ ω, Ψ ω * Ql mk X U ξ b l k ω ∂P = 0 := by
  induction l with
  | zero =>
    intro b Ψ B hΨ hB hT
    have hbT : b ∈ T := by simpa using hT [] rfl
    have hX : Measurable[sgK X U (Kc T k)] (X b) := X_sgK (inl_Kc T k b)
    have hUk : Measurable[sgK X U {Sum.inr (b, k)}] (U b k) := U_sgK rfl
    have hdisj : Disjoint (Kc T k) {Sum.inr (b, k)} :=
      Set.disjoint_singleton_right.2 (fun h => h b hbT rfl)
    have hind : IndepFun (fun ω => (Ψ ω, X b ω)) (U b k) P :=
      indepFun_sgK hgw (hΨ.prodMk hX) hUk hdisj
    have hΨm : Measurable Ψ := hΨ.mono (sgK_le hgw _) le_rfl
    have hYm : Measurable (fun ω => (Ψ ω, X b ω)) := hΨm.prodMk (hgw.measurable_X b)
    have hF : Measurable (fun q : (ℝ × M) × ℝ => q.1.1 * (ξ q.1.2 q.2 - gf ξ q.1.2)) :=
      measurable_fst.fst.mul ((hgw.measurable_ζ.comp (measurable_fst.snd.prodMk measurable_snd)).sub
        ((gf_meas hgw).comp measurable_fst.snd))
    have hint : Integrable (fun ω => Ψ ω * Ql mk X U ξ b 0 k ω) P :=
      intg_of_bdd (hΨm.mul (Ql_meas' hgw b 0 k)) (B * 2) (fun ω => by
        rw [abs_mul]
        exact mul_le_mul (hB ω) (by simpa using Ql_bound hgw b 0 k ω) (abs_nonneg _)
          ((abs_nonneg _).trans (hB ω)))
    have e : (fun ω => Ψ ω * Ql mk X U ξ b 0 k ω)
        = fun ω => (fun q : (ℝ × M) × ℝ => q.1.1 * (ξ q.1.2 q.2 - gf ξ q.1.2))
            ((Ψ ω, X b ω), U b k ω) := by
      funext ω; simp [Ql_zero, Dn, Z]
    rw [e] at hint ⊢
    rw [indep_fubini hind hYm (hgw.measurable_U b k) hF hint (g := fun _ => (0 : ℝ))
      measurable_const (fun a => ?_)]
    · simp
    · have hm : Measurable (fun ω => ξ a.2 (U b k ω)) :=
        (hgw.measurable_ζ.comp measurable_prodMk_left).comp (hgw.measurable_U b k)
      have hi : Integrable (fun ω => ξ a.2 (U b k ω)) P :=
        intg_of_bdd hm 1 (fun ω => abs_le.2 ⟨(hgw.ζ_mem _ _).1, (hgw.ζ_mem _ _).2⟩)
      simp only
      rw [integral_const_mul, integral_sub hi (integrable_const _), int_U hgw b k a.2]
      simp
  | succ l ih =>
    intro b Ψ B hΨ hB hT
    have hX : Measurable[sgK X U (Kc T k)] (X b) := X_sgK (inl_Kc T k b)
    have hΨm : Measurable Ψ := hΨ.mono (sgK_le hgw _) le_rfl
    have hXm := hgw.measurable_X b
    have e : (fun ω => Ψ ω * Ql mk X U ξ b (l + 1) k ω) = fun ω =>
        ∑ j ∈ Finset.range (mk.N (X b ω)), Ψ ω * (mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω) := by
      funext ω; rw [Ql_succ, Finset.mul_sum]
    rw [e]
    have hB0 : ∀ ω, 0 ≤ B := fun ω => (abs_nonneg _).trans (hB ω)
    refine int_rangeSum_zero (fun ω => mk.N (X b ω))
      (fun j ω => Ψ ω * (mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω))
      (fun j ω => B * (c ^ l * 2) * mk.C (X b ω) j) (B * (c ^ l * 2) * c)
      (mk.measurable_N.comp hXm)
      (fun j => hΨm.mul (((mk.measurable_C j).comp hXm).mul (Ql_meas' hgw _ l k)))
      (fun j => ((mk.measurable_C j).comp hXm).const_mul _)
      (fun j ω => ?_) (fun ω => ?_) (fun j => ?_)
    · have hC := hgw.weights_nonneg (X b ω) j
      rw [abs_mul, abs_mul, abs_of_nonneg hC]
      calc |Ψ ω| * (mk.C (X b ω) j * |Ql mk X U ξ (b ++ [j]) l k ω|)
          ≤ B * (mk.C (X b ω) j * (c ^ l * 2)) := by
            gcongr
            · exact hB0 ω
            · exact hB ω
            · exact Ql_bound hgw _ l k ω
        _ = B * (c ^ l * 2) * mk.C (X b ω) j := by ring
    · rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (wsum_le hgw _)
        (mul_nonneg (hB0 ω) (mul_nonneg (pow_nonneg hgw.c_nonneg l) (by norm_num)))
    · have hΨ' : Measurable[sgK X U (Kc T k)]
          (fun ω => Ψ ω * (if j < mk.N (X b ω) then mk.C (X b ω) j else 0)) := by
        let _ := sgK X U (Kc T k)
        exact hΨ.mul (Measurable.ite (measurableSet_lt measurable_const (mk.measurable_N.comp hX))
          ((mk.measurable_C j).comp hX) measurable_const)
      have := ih (b ++ [j]) _ B hΨ' (fun ω => by
          rw [abs_mul]
          have h1 : |(if j < mk.N (X b ω) then mk.C (X b ω) j else 0)| ≤ 1 := by
            split_ifs
            · rw [abs_of_nonneg (hgw.weights_nonneg _ _)]; exact hgw.weights_le_one _ _
            · simp
          calc |Ψ ω| * |(if j < mk.N (X b ω) then mk.C (X b ω) j else 0)| ≤ B * 1 :=
                mul_le_mul (hB ω) h1 (abs_nonneg _) (hB0 ω)
            _ = B := mul_one B)
        (fun t ht => by
          rw [List.append_assoc]; exact hT ([j] ++ t) (by simp [ht]))
      refine (integral_congr_ae (ae_of_all _ (fun ω => ?_))).trans this
      split_ifs <;> ring

lemma Ql_mean [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) (l k : ℕ) :
    ∫ ω, Ql mk X U ξ b l k ω ∂P = 0 := by
  have := orth hgw k Set.univ l b (fun _ => 1) 1 measurable_const (fun _ => by simp)
    (fun _ _ => Set.mem_univ _)
  simpa using this

end sig

/-! ## second moments of the noise layers -/

section mom
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

lemma XU_indep (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ) :
    IndepFun (X b) (U b t) P := by
  rw [IndepFun_iff_Indep]
  exact (fam_iIndep hgw).indep (i := Sum.inl b) (j := Sum.inr (b, t)) (by simp)

lemma XU_map [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ) :
    P.map (fun ω => (X b ω, U b t ω))
      = (P.map (X b)).prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map (hgw.measurable_X b).aemeasurable
    (hgw.measurable_U b t).aemeasurable).1 (XU_indep hgw b t), (hgw.unif b t).map_eq]

lemma XU_ident [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) {b : Label}
    (hb : b ≠ []) (t : ℕ) :
    IdentDistrib (fun ω => (X b ω, U b t ω)) (fun ω => (X [0] ω, U [0] 0 ω)) P P where
  aemeasurable_fst := ((hgw.measurable_X b).prodMk (hgw.measurable_U b t)).aemeasurable
  aemeasurable_snd := ((hgw.measurable_X [0]).prodMk (hgw.measurable_U [0] 0)).aemeasurable
  map_eq := by rw [XU_map hgw, XU_map hgw, (hgw.ident_marks b hb).map_eq]

lemma XU_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) {b : Label}
    (hb : b ≠ []) (t : ℕ) (φ : M × ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, φ (X b ω, U b t ω) ∂P = ∫ ω, φ (X [0] ω, U [0] 0 ω) ∂P :=
  ((XU_ident hgw hb t).comp hφ).integral_eq

lemma XU_int_t [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) (t : ℕ)
    (φ : M × ℝ → ℝ) (hφ : Measurable φ) :
    ∫ ω, φ (X b ω, U b t ω) ∂P = ∫ ω, φ (X b ω, U b 0 ω) ∂P := by
  have h1 : Measurable (fun ω => (X b ω, U b t ω)) :=
    (hgw.measurable_X b).prodMk (hgw.measurable_U b t)
  have h0 : Measurable (fun ω => (X b ω, U b 0 ω)) :=
    (hgw.measurable_X b).prodMk (hgw.measurable_U b 0)
  rw [← integral_map h1.aemeasurable hφ.aestronglyMeasurable,
    ← integral_map h0.aemeasurable hφ.aestronglyMeasurable, XU_map hgw b t, XU_map hgw b 0]

lemma X_int (hgw : GWModel P mk X U ξ c d) {b : Label} (hb : b ≠ []) (φ : M → ℝ)
    (hφ : Measurable φ) : ∫ ω, φ (X b ω) ∂P = ∫ ω, φ (X [0] ω) ∂P :=
  ((hgw.ident_marks b hb).comp hφ).integral_eq

lemma Dn2_meas (hgw : GWModel P mk X U ξ c d) :
    Measurable (fun p : M × ℝ => (ξ p.1 p.2 - gf ξ p.1) ^ 2) :=
  (hgw.measurable_ζ.sub ((gf_meas hgw).comp measurable_fst)).pow_const 2

lemma split_sum (s : Finset ℕ) (j : ℕ) (f : ℕ → ℝ) :
    ∑ x ∈ s, f x = (if j ∈ s then f j else 0) + ∑ x ∈ s, (if x = j then 0 else f x) := by
  have : ∀ x, f x = (if x = j then f x else 0) + (if x = j then 0 else f x) := fun x => by
    split_ifs <;> simp
  conv_lhs => rw [Finset.sum_congr rfl (fun x _ => this x)]
  rw [Finset.sum_add_distrib]
  congr 1
  simp [Finset.sum_ite_eq']

lemma C2_bound (hgw : GWModel P mk X U ξ c d) (x : M) (j : ℕ) : |mk.C x j ^ 2| ≤ mk.C x j := by
  have h0 := hgw.weights_nonneg x j
  have h1 := hgw.weights_le_one x j
  rw [abs_of_nonneg (sq_nonneg _)]; nlinarith

lemma sumC2_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, sumC2 mk X b ω ∂P
      = ∑' j, ∫ ω, (if j < mk.N (X b ω) then mk.C (X b ω) j ^ 2 else 0) ∂P := by
  have hXm := hgw.measurable_X b
  exact int_rangeSum (fun ω => mk.N (X b ω)) (fun j ω => mk.C (X b ω) j ^ 2)
    (fun j ω => mk.C (X b ω) j) c (mk.measurable_N.comp hXm)
    (fun j => ((mk.measurable_C j).comp hXm).pow_const 2) (fun j => (mk.measurable_C j).comp hXm)
    (fun j ω => C2_bound hgw _ j) (fun ω => wsum_le hgw _)

set_option maxHeartbeats 1000000 in
lemma Ql_sq_succ [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label)
    (l k : ℕ) (q : ℝ) (hq : ∀ j, ∫ ω, Ql mk X U ξ (b ++ [j]) l k ω ^ 2 ∂P = q) :
    ∫ ω, Ql mk X U ξ b (l + 1) k ω ^ 2 ∂P = (∫ ω, sumC2 mk X b ω ∂P) * q := by
  have hXm := hgw.measurable_X b
  have hc0 := hgw.c_nonneg
  set Bq := c ^ l * 2 with hBq
  have hBq0 : 0 ≤ Bq := mul_nonneg (pow_nonneg hc0 l) (by norm_num)
  have hQb : ∀ ω, |Ql mk X U ξ b (l + 1) k ω| ≤ c * Bq := fun ω => by
    have := Ql_bound hgw b (l + 1) k ω; rw [pow_succ] at this; linarith
  have e1 : (fun ω => Ql mk X U ξ b (l + 1) k ω ^ 2) = fun ω =>
      ∑ j ∈ Finset.range (mk.N (X b ω)),
        mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω * Ql mk X U ξ b (l + 1) k ω := by
    funext ω; rw [sq, ← Finset.sum_mul, ← Ql_succ]
  rw [e1, int_rangeSum (fun ω => mk.N (X b ω))
    (fun j ω => mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω * Ql mk X U ξ b (l + 1) k ω)
    (fun j ω => mk.C (X b ω) j * (Bq * (c * Bq)))
    (c * (Bq * (c * Bq))) (mk.measurable_N.comp hXm)
    (fun j => (((mk.measurable_C j).comp hXm).mul (Ql_meas' hgw _ l k)).mul
      (Ql_meas' hgw b (l + 1) k))
    (fun j => ((mk.measurable_C j).comp hXm).mul_const _)
    (fun j ω => by
      have hC := hgw.weights_nonneg (X b ω) j
      rw [abs_mul, abs_mul, abs_of_nonneg hC, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (Ql_bound hgw _ l k ω) (hQb ω)
        (abs_nonneg _) hBq0) hC)
    (fun ω => by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (wsum_le hgw _)
        (mul_nonneg hBq0 (mul_nonneg hc0 hBq0)))]
  have e2 : ∀ j, ∫ ω, (if j < mk.N (X b ω) then mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω
        * Ql mk X U ξ b (l + 1) k ω else 0) ∂P
      = (∫ ω, (if j < mk.N (X b ω) then mk.C (X b ω) j ^ 2 else 0) ∂P) * q := by
    intro j
    set Qo : Ω → ℝ := fun ω => ∑ j' ∈ Finset.range (mk.N (X b ω)),
      mk.C (X b ω) j' * (if j' = j then 0 else Ql mk X U ξ (b ++ [j']) l k ω) with hQo
    set ind : Ω → ℝ := fun ω => if j < mk.N (X b ω) then mk.C (X b ω) j else 0 with hind
    set ind2 : Ω → ℝ := fun ω => if j < mk.N (X b ω) then mk.C (X b ω) j ^ 2 else 0 with hind2
    have hsplit : ∀ ω, Ql mk X U ξ b (l + 1) k ω = ind ω * Ql mk X U ξ (b ++ [j]) l k ω + Qo ω := by
      intro ω
      rw [Ql_succ, split_sum _ j]
      congr 1
      · simp only [hind, Finset.mem_range]; split_ifs <;> ring
      · exact Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp)
    have hpt : ∀ ω, (if j < mk.N (X b ω) then mk.C (X b ω) j * Ql mk X U ξ (b ++ [j]) l k ω
        * Ql mk X U ξ b (l + 1) k ω else 0)
        = ind2 ω * Ql mk X U ξ (b ++ [j]) l k ω ^ 2
          + (ind ω * Qo ω) * Ql mk X U ξ (b ++ [j]) l k ω := by
      intro ω; rw [hsplit ω]; simp only [hind, hind2]; split_ifs <;> ring
    have hindm : Measurable ind := Measurable.ite
      (measurableSet_lt measurable_const (mk.measurable_N.comp hXm))
      ((mk.measurable_C j).comp hXm) measurable_const
    have hind2m : Measurable ind2 := Measurable.ite
      (measurableSet_lt measurable_const (mk.measurable_N.comp hXm))
      (((mk.measurable_C j).comp hXm).pow_const 2) measurable_const
    have hindb : ∀ ω, |ind ω| ≤ 1 := fun ω => by
      simp only [hind]; split_ifs
      · rw [abs_of_nonneg (hgw.weights_nonneg _ _)]; exact hgw.weights_le_one _ _
      · simp
    have hind2b : ∀ ω, |ind2 ω| ≤ 1 := fun ω => by
      simp only [hind2]; split_ifs
      · exact (C2_bound hgw _ j).trans (hgw.weights_le_one _ _)
      · simp
    have hQob : ∀ ω, |Qo ω| ≤ c * Bq := fun ω =>
      wabs _ _ _ c Bq (fun j' => hgw.weights_nonneg _ j') (wsum_le hgw _) hBq0 (fun j' => by
        split_ifs
        · simp [hBq0]
        · exact Ql_bound hgw _ l k ω)
    -- measurability of `ind * Qo` for the orthogonality lemma
    set Tj : Set Label := {u | ∃ t : Label, t.length = l ∧ u = (b ++ [j]) ++ t} with hTj
    have hmeas : Measurable[sgK X U (Kc Tj k)] (fun ω => ind ω * Qo ω) := by
      have hX : Measurable[sgK X U (Kc Tj k)] (X b) := X_sgK (inl_Kc _ _ _)
      have hQ : ∀ j', j' ≠ j → Measurable[sgK X U (Kc Tj k)] (Ql mk X U ξ (b ++ [j']) l k) := by
        intro j' h
        refine (Ql_meas hgw k l (b ++ [j'])).mono (sgK_mono (Ksub_Kc ?_)) le_rfl
        rintro t _ _ ⟨t', _, heq⟩
        simp only [List.append_assoc, List.append_cancel_left_eq, List.singleton_append,
          List.cons.injEq] at heq
        exact h heq.1
      have hV : Measurable[sgK X U (Kc Tj k)]
          (fun ω j' => if j' = j then 0 else Ql mk X U ξ (b ++ [j']) l k ω) := by
        let _ := sgK X U (Kc Tj k)
        refine measurable_pi_lambda _ (fun j' => ?_)
        by_cases h : j' = j
        · simp only [h, ↓reduceIte]; exact measurable_const
        · simp only [h, ↓reduceIte]; exact hQ j' h
      let _ := sgK X U (Kc Tj k)
      have h1 : Measurable[sgK X U (Kc Tj k)] ind := Measurable.ite
        (measurableSet_lt measurable_const (mk.measurable_N.comp hX))
        ((mk.measurable_C j).comp hX) measurable_const
      exact h1.mul (meas_Hs.comp (hX.prodMk hV))
    have h0 : ∫ ω, (ind ω * Qo ω) * Ql mk X U ξ (b ++ [j]) l k ω ∂P = 0 :=
      orth hgw k Tj l (b ++ [j]) (fun ω => ind ω * Qo ω) (c * Bq) hmeas
        (fun ω => by
          rw [abs_mul]
          calc |ind ω| * |Qo ω| ≤ 1 * (c * Bq) :=
                mul_le_mul (hindb ω) (hQob ω) (abs_nonneg _) zero_le_one
            _ = c * Bq := one_mul _)
        (fun t ht => ⟨t, ht, rfl⟩)
    have hQjm := Ql_meas' hgw (b ++ [j]) l k
    have hQall : ∀ j', Measurable (Ql mk X U ξ (b ++ [j']) l k) := fun j' => Ql_meas' hgw _ l k
    have hVm : Measurable (fun ω j' => if j' = j then (0 : ℝ)
        else Ql mk X U ξ (b ++ [j']) l k ω) := measurable_pi_lambda _ (fun j' => by
      by_cases h : j' = j
      · simp only [h, ↓reduceIte]; exact measurable_const
      · simp only [h, ↓reduceIte]; exact hQall j')
    have hQom : Measurable Qo := meas_Hs.comp (hXm.prodMk hVm)
    have i1 : Integrable (fun ω => ind2 ω * Ql mk X U ξ (b ++ [j]) l k ω ^ 2) P :=
      intg_of_bdd (hind2m.mul (hQjm.pow_const 2)) (1 * Bq ^ 2) (fun ω => by
        rw [abs_mul, abs_pow]
        exact mul_le_mul (hind2b ω) (pow_le_pow_left₀ (abs_nonneg _) (Ql_bound hgw _ l k ω) 2)
          (by positivity) zero_le_one)
    have i2 : Integrable (fun ω => (ind ω * Qo ω) * Ql mk X U ξ (b ++ [j]) l k ω) P :=
      intg_of_bdd ((hindm.mul hQom).mul hQjm) (1 * (c * Bq) * Bq) (fun ω => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hindb ω) (hQob ω) (abs_nonneg _) zero_le_one)
          (Ql_bound hgw _ l k ω) (abs_nonneg _) (by positivity))
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add i1 i2, h0, add_zero]
    -- independence of the mark of `b` and the subtree of `b ++ [j]`
    have hm1 : Measurable[sgK X U {Sum.inl b}] ind2 := by
      have hX : Measurable[sgK X U {Sum.inl b}] (X b) := X_sgK rfl
      let _ := sgK X U {Sum.inl b}
      exact Measurable.ite (measurableSet_lt measurable_const (mk.measurable_N.comp hX))
        (((mk.measurable_C j).comp hX).pow_const 2) measurable_const
    have hm2 : Measurable[sgK X U (Ksub (b ++ [j]) l k)]
        (fun ω => Ql mk X U ξ (b ++ [j]) l k ω ^ 2) := by
      have hQ2 := Ql_meas hgw k l (b ++ [j])
      let _ := sgK X U (Ksub (b ++ [j]) l k)
      exact hQ2.pow_const 2
    have hdisj : Disjoint ({Sum.inl b} : Set Key) (Ksub (b ++ [j]) l k) := by
      refine Set.disjoint_singleton_left.2 ?_
      rintro (⟨u, hu, hpre⟩ | ⟨t, _, h⟩)
      · simp only [Sum.inl.injEq] at hu
        subst hu
        have := hpre.length_le
        simp at this
      · simp at h
    have hI := indepFun_sgK hgw hm1 hm2 hdisj
    have := hI.integral_mul_eq_mul_integral hind2m.aestronglyMeasurable
      (hQjm.pow_const 2).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hq j]
  rw [tsum_congr e2, tsum_mul_right, sumC2_int hgw b]

lemma Ql_sq [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (k l : ℕ) :
    ∀ b : Label, b ≠ [] → ∫ ω, Ql mk X U ξ b l k ω ^ 2 ∂P
      = DirectedOpinion.NoMemory.rho2 P mk X ^ l * ∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P := by
  induction l with
  | zero =>
    intro b hb
    simp only [pow_zero, one_mul, Ql_zero]
    exact XU_int hgw hb k (fun p => (ξ p.1 p.2 - gf ξ p.1) ^ 2) (Dn2_meas hgw)
  | succ l ih =>
    intro b hb
    rw [Ql_sq_succ hgw b l k _ (fun j => ih (b ++ [j]) (by simp))]
    have : ∫ ω, sumC2 mk X b ω ∂P = DirectedOpinion.NoMemory.rho2 P mk X :=
      X_int hgw hb (fun x => ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2)
        (meas_rangeSum _ _ mk.measurable_N (fun j => (mk.measurable_C j).pow_const 2))
    rw [this, pow_succ]; ring

lemma Ql_sq_root0 [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (k : ℕ) :
    ∫ ω, Ql mk X U ξ [] 0 k ω ^ 2 ∂P = ∫ ω, Dn X U ξ [] 0 ω ^ 2 ∂P := by
  simp only [Ql_zero]
  exact XU_int_t hgw [] k (fun p => (ξ p.1 p.2 - gf ξ p.1) ^ 2) (Dn2_meas hgw)

lemma Ql_sq_root [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (k l : ℕ) :
    ∫ ω, Ql mk X U ξ [] (l + 1) k ω ^ 2 ∂P
      = rho2star P mk X * (DirectedOpinion.NoMemory.rho2 P mk X ^ l
          * ∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P) := by
  rw [Ql_sq_succ hgw [] l k _ (fun j => Ql_sq hgw k l ([] ++ [j]) (by simp))]
  rfl

end mom

/-! ## the noise series -/

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

lemma int_mul_tsum {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (H : Ω → ℝ) (K r B : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hG : ∀ s, Measurable (G s)) (hGb : ∀ s ω, |G s ω| ≤ r ^ s * K) (hH : Measurable H)
    (hHb : ∀ ω, |H ω| ≤ B) :
    ∫ ω, H ω * ∑' s, G s ω ∂P = ∑' s, ∫ ω, H ω * G s ω ∂P := by
  have e : ∀ ω, H ω * ∑' s, G s ω = ∑' s, H ω * G s ω := fun ω => tsum_mul_left.symm
  rw [integral_congr_ae (ae_of_all _ e)]
  have hb : ∀ s ω, ‖H ω * G s ω‖ ≤ B * (r ^ s * K) := fun s ω => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hHb ω) (hGb s ω) (abs_nonneg _) ((abs_nonneg _).trans (hHb ω))
  have hint : ∀ s, Integrable (fun ω => H ω * G s ω) P := fun s =>
    intg_of_bdd (hH.mul (hG s)) (B * (r ^ s * K)) (fun ω => by simpa using hb s ω)
  refine (integral_tsum_of_summable_integral_norm hint ?_).symm
  refine Summable.of_nonneg_of_le (fun s => integral_nonneg (fun ω => norm_nonneg _))
    (fun s => ?_) ((summable_geometric_of_lt_one hr0 hr1).mul_left (B * K))
  calc ∫ ω, ‖H ω * G s ω‖ ∂P ≤ ∫ _ω, B * (r ^ s * K) ∂P :=
        integral_mono (hint s).norm (integrable_const _) (fun ω => hb s ω)
    _ = B * K * r ^ s := by rw [integral_const]; simp; ring

section nz
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

omit [MeasurableSpace Ω] in
lemma Gs_eq (b : Label) (s : ℕ) (ω : Ω) : Gs mk X U ξ c d b s ω
    = ∑ l ∈ Finset.range (s + 1), aCoef c d l s * Ql mk X U ξ b l s ω := by
  unfold Gs Ql; rw [iter_binom]; rfl

lemma Gs_meas_K (hgw : GWModel P mk X U ξ c d) (b : Label) (s : ℕ) {K : Set Key}
    (h : ∀ l, Ksub b l s ⊆ K) : Measurable[sgK X U K] (Gs mk X U ξ c d b s) := by
  have e : Gs mk X U ξ c d b s = fun ω => ∑ l ∈ Finset.range (s + 1),
      aCoef c d l s * Ql mk X U ξ b l s ω := funext (Gs_eq b s)
  have hQ : ∀ l, Measurable[sgK X U K] (Ql mk X U ξ b l s) := fun l =>
    (Ql_meas hgw s l b).mono (sgK_mono (h l)) le_rfl
  rw [e]
  let _ := sgK X U K
  exact Finset.measurable_sum _ (fun l _ => (hQ l).const_mul _)

lemma Gs_meas' (hgw : GWModel P mk X U ξ c d) (b : Label) (s : ℕ) :
    Measurable (Gs mk X U ξ c d b s) :=
  (Gs_meas_K hgw b s (K := Set.univ) (fun _ => Set.subset_univ _)).mono (sgK_le hgw _) le_rfl

lemma Ψ_Gs [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) (s : ℕ)
    (Ψ : Ω → ℝ) (B : ℝ) (hΨ : Measurable[sgK X U (Kc Set.univ s)] Ψ) (hB : ∀ ω, |Ψ ω| ≤ B) :
    ∫ ω, Ψ ω * Gs mk X U ξ c d b s ω ∂P = 0 := by
  have hΨm : Measurable Ψ := hΨ.mono (sgK_le hgw _) le_rfl
  have e : (fun ω => Ψ ω * Gs mk X U ξ c d b s ω) = fun ω => ∑ l ∈ Finset.range (s + 1),
      aCoef c d l s * (Ψ ω * Ql mk X U ξ b l s ω) := by
    funext ω; rw [Gs_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hint : ∀ l, Integrable (fun ω => Ψ ω * Ql mk X U ξ b l s ω) P := fun l =>
    intg_of_bdd (hΨm.mul (Ql_meas' hgw b l s)) (B * (c ^ l * 2)) (fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hB ω) (Ql_bound hgw b l s ω) (abs_nonneg _)
        ((abs_nonneg _).trans (hB ω)))
  rw [e, integral_finsetSum _ (fun l _ => (hint l).const_mul _)]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  rw [integral_const_mul, orth hgw s Set.univ l b Ψ B hΨ hB (fun _ _ => Set.mem_univ _),
    mul_zero]

lemma Gs_orth [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) {s s' : ℕ}
    (hss : s ≠ s') : ∫ ω, Gs mk X U ξ c d b s ω * Gs mk X U ξ c d b s' ω ∂P = 0 :=
  Ψ_Gs hgw b s' _ 2 (Gs_meas_K hgw b s (fun l => Ksub_Kc (fun _ _ hk => absurd hk hss)))
    (fun ω => (Gs_bound hgw b s ω).trans (by
      have := pow_le_one₀ (one_sub_d hgw).1 (one_sub_d hgw).2.le (n := s); nlinarith))

lemma Gs_sq [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) (s : ℕ) :
    ∫ ω, Gs mk X U ξ c d b s ω ^ 2 ∂P
      = ∑ l ∈ Finset.range (s + 1), aCoef c d l s ^ 2 * ∫ ω, Ql mk X U ξ b l s ω ^ 2 ∂P := by
  have e : (fun ω => Gs mk X U ξ c d b s ω ^ 2) = fun ω =>
      (0 + ∑ l ∈ Finset.range (s + 1), aCoef c d l s * Ql mk X U ξ b l s ω) ^ 2 := by
    funext ω; rw [Gs_eq, zero_add]
  have hQb : ∀ l ω, |Ql mk X U ξ b l s ω| ≤ 2 := fun l ω => (Ql_bound hgw b l s ω).trans (by
    have := pow_le_one₀ hgw.c_nonneg hgw.c_lt_one.le (n := l); nlinarith)
  rw [e, sq_expand (Finset.range (s + 1)) 0 (fun l => aCoef c d l s)
    (fun l ω => Ql mk X U ξ b l s ω) 2 (by norm_num) (fun l => Ql_meas' hgw b l s) hQb
    (fun l => Ql_mean hgw b l s) (fun l l' hll => ?_)]
  · simp
  · refine orth hgw s {u | ∃ t : Label, t.length = l' ∧ u = b ++ t} l' b _ (c ^ l * 2)
      ((Ql_meas hgw s l b).mono (sgK_mono (Ksub_Kc ?_)) le_rfl) (fun ω => Ql_bound hgw b l s ω)
      (fun t ht => ⟨t, ht, rfl⟩)
    rintro t ht _ ⟨t', ht', heq⟩
    rw [List.append_cancel_left_eq] at heq
    subst heq
    exact hll (ht.symm.trans ht')

/-- the signal part is a function of the marks of the subtree. -/
def KX (b : Label) : Set Key := {e | ∃ u, e = Sum.inl u ∧ b <+: u}

noncomputable def Ay (mk : MarkFns M) (X : Label → Ω → M) (ξ : M → ℝ → ℝ) (l : ℕ) (b : Label)
    (ω : Ω) : ℝ :=
  (treeOp (nAt mk X ω) (wAt mk X ω) 0)^[l] (fun i => gf ξ (X i ω)) b

lemma inl_KX (b : Label) : (Sum.inl b : Key) ∈ KX b := ⟨b, rfl, List.prefix_refl b⟩

lemma KX_child (b : Label) (j : ℕ) : KX (b ++ [j]) ⊆ KX b := by
  rintro e ⟨u, rfl, hu⟩; exact ⟨u, rfl, (List.prefix_append b [j]).trans hu⟩

lemma Ay_meas (hgw : GWModel P mk X U ξ c d) (l : ℕ) :
    ∀ b, Measurable[sgK X U (KX b)] (Ay mk X ξ l b) := by
  induction l with
  | zero =>
    intro b
    have : Ay mk X ξ 0 b = fun ω => gf ξ (X b ω) := by funext ω; simp [Ay]
    rw [this]
    exact (gf_meas' hgw.measurable_ζ).comp (X_sgK (inl_KX b))
  | succ l ih =>
    intro b
    have e : Ay mk X ξ (l + 1) b = (fun p : M × (ℕ → ℝ) =>
        ∑ j ∈ Finset.range (mk.N p.1), mk.C p.1 j * p.2 j) ∘
        (fun ω => (X b ω, fun j => Ay mk X ξ l (b ++ [j]) ω)) := by
      funext ω; unfold Ay; rw [treeOp_zero_succ]; rfl
    rw [e]
    have hV : Measurable[sgK X U (KX b)] (fun ω j => Ay mk X ξ l (b ++ [j]) ω) := by
      let _ := sgK X U (KX b)
      exact measurable_pi_lambda _
        (fun j => (ih (b ++ [j])).mono (sgK_mono (KX_child b j)) le_rfl)
    exact meas_Hs.comp ((X_sgK (inl_KX b)).prodMk hV)

lemma Ry_meas (hgw : GWModel P mk X U ξ c d) (b : Label) :
    Measurable[sgK X U (KX b)] (Ry mk X ξ c d b) := by
  have hA : ∀ s, Measurable[sgK X U (KX b)] (fun ω =>
      (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => gf ξ (X i ω)) b) := by
    intro s
    have e : (fun ω => (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s]
        (fun i => gf ξ (X i ω)) b) = fun ω => ∑ l ∈ Finset.range (s + 1),
          aCoef c d l s * Ay mk X ξ l b ω := by
      funext ω; rw [iter_binom]; rfl
    have hAy := fun l => Ay_meas hgw l b
    rw [e]
    let _ := sgK X U (KX b)
    exact Finset.measurable_sum _ (fun l _ => (hAy l).const_mul _)
  refine @measurable_of_tendsto_metrizable Ω ℝ (sgK X U (KX b)) _ _ _ _
    (fun n ω => ∑ s ∈ Finset.range n,
      (treeOp (nAt mk X ω) (wAt mk X ω) (1 - c - d))^[s] (fun i => gf ξ (X i ω)) b) _
    (fun n => ?_) ?_
  · let _ := sgK X U (KX b)
    exact Finset.measurable_sum (Finset.range n) (fun s _ => hA s)
  · exact tendsto_pi_nhds.2 (fun ω => (Ry_summable hgw b ω).hasSum.tendsto_sum_nat)

lemma Ry_meas' (hgw : GWModel P mk X U ξ c d) (b : Label) : Measurable (Ry mk X ξ c d b) :=
  (Ry_meas hgw b).mono (sgK_le hgw _) le_rfl

lemma Ry_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    |Ry mk X ξ c d b ω| ≤ d⁻¹ := by
  unfold Ry
  have := tsum_of_norm_bounded (hasSum_geometric_of_lt_one (one_sub_d hgw).1 (one_sub_d hgw).2)
    (fun s => by
      rw [Real.norm_eq_abs, ← mul_one ((1 - d) ^ s)]
      exact Del_bound hgw (fun i => gf ξ (X i ω)) 1 (fun i => gf_bound hgw _) s b ω)
  rw [Real.norm_eq_abs, sub_sub_cancel] at this
  exact this

lemma Nz_bound (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) :
    |Nz mk X U ξ c d b ω| ≤ d⁻¹ * 2 := by
  have := tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (one_sub_d hgw).1
    (one_sub_d hgw).2).mul_right 2)
    (fun s => by rw [Real.norm_eq_abs]; exact Gs_bound hgw b s ω)
  rw [Real.norm_eq_abs, sub_sub_cancel] at this
  exact this

lemma Nz_meas (hgw : GWModel P mk X U ξ c d) (b : Label) : Measurable (Nz mk X U ξ c d b) := by
  exact measurable_of_tendsto_metrizable
    (fun n => Finset.measurable_sum (Finset.range n) (fun s _ => Gs_meas' hgw b s))
    (tendsto_pi_nhds.2 (fun ω => (Gs_summable hgw b ω).hasSum.tendsto_sum_nat))

lemma KX_Kc (b : Label) (T : Set Label) (k : ℕ) : KX b ⊆ Kc T k := by
  rintro e ⟨u, rfl, _⟩; exact inl_Kc T k u

lemma Ψ_Nz [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label)
    (Ψ : Ω → ℝ) (B : ℝ) (hΨ : ∀ s, Measurable[sgK X U (Kc Set.univ s)] Ψ)
    (hB : ∀ ω, |Ψ ω| ≤ B) : ∫ ω, Ψ ω * Nz mk X U ξ c d b ω ∂P = 0 := by
  unfold Nz
  rw [int_mul_tsum (fun s => Gs mk X U ξ c d b s) Ψ 2 (1 - d) B (one_sub_d hgw).1
    (one_sub_d hgw).2 (Gs_meas' hgw b) (Gs_bound hgw b) ((hΨ 0).mono (sgK_le hgw _) le_rfl) hB]
  simp [Ψ_Gs hgw b _ Ψ B (hΨ _) hB]

lemma Nz_mean [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, Nz mk X U ξ c d b ω ∂P = 0 := by
  simpa using Ψ_Nz hgw b (fun _ => 1) 1 (fun _ => measurable_const) (fun _ => by simp)

lemma Ry_Nz [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, Ry mk X ξ c d b ω * Nz mk X U ξ c d b ω ∂P = 0 :=
  Ψ_Nz hgw b _ d⁻¹ (fun s => (Ry_meas hgw b).mono (sgK_mono (KX_Kc b _ s)) le_rfl)
    (Ry_bound hgw b)

lemma Nz_sq [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, Nz mk X U ξ c d b ω ^ 2 ∂P = ∑' s, ∫ ω, Gs mk X U ξ c d b s ω ^ 2 ∂P := by
  have e : (fun ω => Nz mk X U ξ c d b ω ^ 2)
      = fun ω => Nz mk X U ξ c d b ω * ∑' s, Gs mk X U ξ c d b s ω := by
    funext ω; rw [sq]; rfl
  rw [e, int_mul_tsum (fun s => Gs mk X U ξ c d b s) _ 2 (1 - d) (d⁻¹ * 2) (one_sub_d hgw).1
    (one_sub_d hgw).2 (Gs_meas' hgw b) (Gs_bound hgw b) (Nz_meas hgw b) (Nz_bound hgw b)]
  refine tsum_congr (fun s => ?_)
  have e2 : (fun ω => Nz mk X U ξ c d b ω * Gs mk X U ξ c d b s ω)
      = fun ω => Gs mk X U ξ c d b s ω * ∑' s', Gs mk X U ξ c d b s' ω := by
    funext ω; rw [mul_comm]; rfl
  have hGsb : ∀ ω, |Gs mk X U ξ c d b s ω| ≤ 2 := fun ω => (Gs_bound hgw b s ω).trans (by
      have := pow_le_one₀ (one_sub_d hgw).1 (one_sub_d hgw).2.le (n := s); nlinarith)
  rw [e2, int_mul_tsum (fun s => Gs mk X U ξ c d b s) _ 2 (1 - d) 2 (one_sub_d hgw).1
    (one_sub_d hgw).2 (Gs_meas' hgw b) (Gs_bound hgw b) (Gs_meas' hgw b s) hGsb,
    tsum_eq_single s (fun s' hs' => Gs_orth hgw b (Ne.symm hs'))]
  congr 1; funext ω; rw [sq]

end nz

/-! ## moments of the signal part -/

lemma zero_of_le_pow {q K x : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (h : ∀ k : ℕ, |x| ≤ q ^ k * K) :
    x = 0 := by
  have ht : Filter.Tendsto (fun k : ℕ => q ^ k * K) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const K
  have : |x| ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall h)
  exact abs_nonpos_iff.1 this

section ry
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

def KXc (b : Label) : Set Key := {e | ∃ u j, e = Sum.inl u ∧ b ++ [j] <+: u}

lemma KX_child_c (b : Label) (j : ℕ) : KX (b ++ [j]) ⊆ KXc b := by
  rintro e ⟨u, rfl, hu⟩; exact ⟨u, j, rfl, hu⟩

lemma disj_self_KXc (b : Label) : Disjoint ({Sum.inl b} : Set Key) (KXc b) := by
  refine Set.disjoint_singleton_left.2 ?_
  rintro ⟨u, j, hu, hpre⟩
  simp only [Sum.inl.injEq] at hu
  subst hu
  have := hpre.length_le
  simp at this

lemma disj_KX_children (b : Label) {j j' : ℕ} (h : j ≠ j') :
    Disjoint (KX (b ++ [j])) (KX (b ++ [j'])) := by
  refine Set.disjoint_left.2 ?_
  rintro e ⟨u, rfl, h1⟩ ⟨u', hu', h2⟩
  simp only [Sum.inl.injEq] at hu'
  subst hu'
  have hl : (b ++ [j]).length ≤ (b ++ [j']).length := by simp
  have := (List.prefix_of_prefix_length_le h1 h2 hl).eq_of_length (by simp)
  simp at this
  exact h this

lemma Vry_meas (hgw : GWModel P mk X U ξ c d) (b : Label) :
    Measurable[sgK X U (KXc b)] (fun ω j => Ry mk X ξ c d (b ++ [j]) ω) := by
  have h : ∀ j, Measurable[sgK X U (KXc b)] (Ry mk X ξ c d (b ++ [j])) := fun j =>
    (Ry_meas hgw _).mono (sgK_mono (KX_child_c b j)) le_rfl
  let _ := sgK X U (KXc b)
  exact measurable_pi_lambda _ h

lemma Vry_meas' (hgw : GWModel P mk X U ξ c d) (b : Label) :
    Measurable (fun ω j => Ry mk X ξ c d (b ++ [j]) ω) :=
  (Vry_meas hgw b).mono (sgK_le hgw _) le_rfl

lemma XV_indep (hgw : GWModel P mk X U ξ c d) (b : Label) :
    IndepFun (X b) (fun ω j => Ry mk X ξ c d (b ++ [j]) ω) P :=
  indepFun_sgK hgw (X_sgK (Set.mem_singleton _)) (Vry_meas hgw b) (disj_self_KXc b)

lemma Ry_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    Integrable (Ry mk X ξ c d b) P :=
  intg_of_bdd (Ry_meas' hgw b) _ (Ry_bound hgw b)

lemma sumC_le (hgw : GWModel P mk X U ξ c d) (b : Label) (ω : Ω) : |sumC mk X b ω| ≤ c := by
  unfold sumC
  rw [abs_of_nonneg (wsum_nonneg hgw _)]; exact wsum_le hgw _

lemma sumC_meas (hgw : GWModel P mk X U ξ c d) (b : Label) : Measurable (sumC mk X b) :=
  meas_rangeSum (fun ω => mk.N (X b ω)) (fun j ω => mk.C (X b ω) j)
    (mk.measurable_N.comp (hgw.measurable_X b)) (fun j => (mk.measurable_C j).comp (hgw.measurable_X b))

lemma wsum2_le_sq (hgw : GWModel P mk X U ξ c d) (x : M) :
    ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 ≤ c ^ 2 := by
  have hS0 := wsum_nonneg hgw x
  have hS := wsum_le hgw x
  calc ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2
      ≤ ∑ j ∈ Finset.range (mk.N x), mk.C x j * ∑ j' ∈ Finset.range (mk.N x), mk.C x j' :=
        Finset.sum_le_sum (fun j hj => by
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun j' _ => hgw.weights_nonneg x j') hj)
            (hgw.weights_nonneg x j))
    _ = (∑ j ∈ Finset.range (mk.N x), mk.C x j) ^ 2 := by rw [← Finset.sum_mul, sq]
    _ ≤ c ^ 2 := pow_le_pow_left₀ hS0 hS 2

lemma ry_mean_formula [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    (c + d) * ∫ ω, Ry mk X ξ c d b ω ∂P = ∫ ω, (gf ξ (X b ω)
      + ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j * ∫ ω', Ry mk X ξ c d (b ++ [j]) ω' ∂P) ∂P := by
  set m : ℕ → ℝ := fun j => ∫ ω', Ry mk X ξ c d (b ++ [j]) ω' ∂P with hm
  have hF : Measurable (fun q : M × (ℕ → ℝ) =>
      gf ξ q.1 + ∑ j ∈ Finset.range (mk.N q.1), mk.C q.1 j * q.2 j) :=
    ((gf_meas hgw).comp measurable_fst).add meas_Hs
  have hg : Measurable (fun x : M => gf ξ x + ∑ j ∈ Finset.range (mk.N x), mk.C x j * m j) :=
    (gf_meas hgw).add (meas_rangeSum _ _ mk.measurable_N (fun j => (mk.measurable_C j).mul_const _))
  have e : ∀ ω, (c + d) * Ry mk X ξ c d b ω = (fun q : M × (ℕ → ℝ) =>
      gf ξ q.1 + ∑ j ∈ Finset.range (mk.N q.1), mk.C q.1 j * q.2 j)
        (X b ω, fun j => Ry mk X ξ c d (b ++ [j]) ω) := fun ω => Ry_rec hgw b ω
  rw [← integral_const_mul, integral_congr_ae (ae_of_all _ e)]
  refine indep_fubini (XV_indep hgw b) (hgw.measurable_X b) (Vry_meas' hgw b) hF ?_ hg
    (fun a => ?_)
  · exact ((Ry_int hgw b).const_mul _).congr (ae_of_all _ e)
  · simp only
    rw [integral_add (integrable_const _)
        (integrable_finsetSum _ (fun j _ => (Ry_int hgw _).const_mul _)),
      integral_const, integral_finsetSum _ (fun j _ => (Ry_int hgw _).const_mul _)]
    simp [integral_const_mul, hm]

lemma rho1_le (hgw : GWModel P mk X U ξ c d) [IsProbabilityMeasure P] :
    0 ≤ rho1 P mk X ∧ rho1 P mk X ≤ c :=
  ⟨integral_nonneg (fun ω => wsum_nonneg hgw _),
    (le_abs_self _).trans (abs_int_le c (sumC_le hgw [0]))⟩

lemma rho2_le (hgw : GWModel P mk X U ξ c d) [IsProbabilityMeasure P] :
    0 ≤ DirectedOpinion.NoMemory.rho2 P mk X ∧ DirectedOpinion.NoMemory.rho2 P mk X ≤ c ^ 2 :=
  ⟨integral_nonneg (fun ω => Finset.sum_nonneg (fun j _ => sq_nonneg _)),
    (le_abs_self _).trans (abs_int_le (c ^ 2) (fun ω => by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
      exact wsum2_le_sq hgw _))⟩

lemma sumC_int (hgw : GWModel P mk X U ξ c d) {b : Label} (hb : b ≠ []) :
    ∫ ω, sumC mk X b ω ∂P = rho1 P mk X :=
  X_int hgw hb (fun x => ∑ j ∈ Finset.range (mk.N x), mk.C x j)
    (meas_rangeSum _ _ mk.measurable_N (fun j => mk.measurable_C j))

set_option maxHeartbeats 1000000 in
lemma ry_mean_child [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label)
    (hb : b ≠ []) : ∫ ω, Ry mk X ξ c d b ω ∂P
      = (∫ ω, gf ξ (X [0] ω) ∂P) / (c + d - rho1 P mk X) := by
  set Eg := ∫ ω, gf ξ (X [0] ω) ∂P with hEg
  set ρ1 := rho1 P mk X with hρ1
  have hd := hgw.d_pos
  have hc0 := hgw.c_nonneg
  obtain ⟨h10, h1c⟩ := rho1_le hgw
  have hCD : 0 < c + d := by linarith
  have hden : 0 < c + d - ρ1 := by linarith
  set μ := Eg / (c + d - ρ1) with hμdef
  have hμ : (c + d) * μ = Eg + ρ1 * μ := by rw [hμdef]; field_simp; ring
  set r := c / (c + d) with hr
  have hr0 : 0 ≤ r := div_nonneg hc0 hCD.le
  have hr1 : r < 1 := (div_lt_one hCD).2 (by linarith)
  set K := d⁻¹ + |μ| with hK
  have hK0 : 0 ≤ K := by positivity
  have hU : P.real Set.univ = 1 := by simp
  have claim : ∀ k : ℕ, ∀ b : Label, b ≠ [] →
      |∫ ω, Ry mk X ξ c d b ω ∂P - μ| ≤ r ^ k * K := by
    intro k
    induction k with
    | zero =>
      intro b _
      rw [pow_zero, one_mul]
      exact (abs_sub _ _).trans (add_le_add (abs_int_le _ (Ry_bound hgw b)) le_rfl)
    | succ k ih =>
      intro b hb
      have hf := ry_mean_formula hgw b
      set m : ℕ → ℝ := fun j => ∫ ω', Ry mk X ξ c d (b ++ [j]) ω' ∂P with hm
      have he : ∀ j, |m j - μ| ≤ r ^ k * K := fun j => ih (b ++ [j]) (by simp)
      have hrk : 0 ≤ r ^ k * K := mul_nonneg (pow_nonneg hr0 k) hK0
      have hXm := hgw.measurable_X b
      have i1 : Integrable (fun ω => gf ξ (X b ω)) P :=
        intg_of_bdd ((gf_meas hgw).comp hXm) 1 (fun ω => gf_bound hgw _)
      have i2 : Integrable (fun ω => ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j * (m j - μ)) P :=
        intg_of_bdd (meas_rangeSum _ _ (mk.measurable_N.comp hXm)
          (fun j => ((mk.measurable_C j).comp hXm).mul_const _)) (c * (r ^ k * K))
          (fun ω => wabs _ _ _ c _ (fun j => hgw.weights_nonneg _ j) (wsum_le hgw _) hrk he)
      have i3 : Integrable (fun ω => μ * sumC mk X b ω) P :=
        (intg_of_bdd (sumC_meas hgw b) c (sumC_le hgw b)).const_mul _
      have e : ∀ ω, gf ξ (X b ω) + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * m j
          = gf ξ (X b ω) + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * (m j - μ)
            + μ * sumC mk X b ω := by
        intro ω
        simp only [sumC, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        have : ∀ j, μ * mk.C (X b ω) j = mk.C (X b ω) j * μ := fun j => mul_comm _ _
        simp only [this]; ring
      have i12 : Integrable (fun ω => gf ξ (X b ω) + ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j * (m j - μ)) P := i1.add i2
      rw [integral_congr_ae (ae_of_all _ e), integral_add i12 i3, integral_add i1 i2,
        integral_const_mul, sumC_int hgw hb,
        X_int hgw hb (gf ξ) (gf_meas hgw)] at hf
      set I := ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j * (m j - μ) ∂P with hI
      have hIb : |I| ≤ c * (r ^ k * K) :=
        abs_int_le _ (fun ω => wabs _ _ _ c _ (fun j => hgw.weights_nonneg _ j)
          (wsum_le hgw _) hrk he)
      have h2 : ∫ ω, Ry mk X ξ c d b ω ∂P - μ = I / (c + d) := by
        field_simp; linarith
      rw [h2, abs_div, abs_of_pos hCD, div_le_iff₀ hCD, pow_succ]
      calc |I| ≤ c * (r ^ k * K) := hIb
        _ = r ^ k * r * K * (c + d) := by rw [hr]; field_simp
  have := zero_of_le_pow hr0 hr1 (fun k => claim k b hb)
  linarith


set_option maxHeartbeats 1000000 in
lemma ry_var_formula [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label)
    (μ M0 : ℝ) (hm : ∀ j, ∫ ω, Ry mk X ξ c d (b ++ [j]) ω ∂P = μ) :
    (c + d) ^ 2 * ∫ ω, (Ry mk X ξ c d b ω - M0) ^ 2 ∂P
      = ∫ ω, ((gf ξ (X b ω) + μ * sumC mk X b ω - (c + d) * M0) ^ 2
        + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2
            * ∫ ω', (Ry mk X ξ c d (b ++ [j]) ω' - μ) ^ 2 ∂P) ∂P := by
  set v : ℕ → ℝ := fun j => ∫ ω', (Ry mk X ξ c d (b ++ [j]) ω' - μ) ^ 2 ∂P with hv
  have hd := hgw.d_pos
  set B := d⁻¹ + |μ| with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hDB : ∀ j ω, |Ry mk X ξ c d (b ++ [j]) ω - μ| ≤ B := fun j ω =>
    (abs_sub _ _).trans (add_le_add (Ry_bound hgw _ ω) le_rfl)
  have hF : Measurable (fun q : M × (ℕ → ℝ) =>
      (gf ξ q.1 + ∑ j ∈ Finset.range (mk.N q.1), mk.C q.1 j * q.2 j - (c + d) * M0) ^ 2) :=
    ((((gf_meas hgw).comp measurable_fst).add meas_Hs).sub_const _).pow_const 2
  have hSm : Measurable (fun x : M => ∑ j ∈ Finset.range (mk.N x), mk.C x j) :=
    meas_rangeSum _ _ mk.measurable_N (fun j => mk.measurable_C j)
  have hg : Measurable (fun x : M =>
      (gf ξ x + μ * ∑ j ∈ Finset.range (mk.N x), mk.C x j - (c + d) * M0) ^ 2
      + ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2 * v j) :=
    ((((gf_meas hgw).add (hSm.const_mul μ)).sub_const _).pow_const 2).add
      (meas_rangeSum _ _ mk.measurable_N (fun j => ((mk.measurable_C j).pow_const 2).mul_const _))
  have e : ∀ ω, (c + d) ^ 2 * (Ry mk X ξ c d b ω - M0) ^ 2 = (fun q : M × (ℕ → ℝ) =>
      (gf ξ q.1 + ∑ j ∈ Finset.range (mk.N q.1), mk.C q.1 j * q.2 j - (c + d) * M0) ^ 2)
        (X b ω, fun j => Ry mk X ξ c d (b ++ [j]) ω) := by
    intro ω
    show _ = (gf ξ (X b ω) + ∑ j ∈ Finset.range (mk.N (X b ω)),
      mk.C (X b ω) j * Ry mk X ξ c d (b ++ [j]) ω - (c + d) * M0) ^ 2
    rw [← Ry_rec hgw b ω]; ring
  have h0 : ∀ j, ∫ ω, (Ry mk X ξ c d (b ++ [j]) ω - μ) ∂P = 0 := by
    intro j
    rw [integral_sub (Ry_int hgw _) (integrable_const _), integral_const, hm j]; simp
  have hind : ∀ j j', j ≠ j' → ∫ ω, (Ry mk X ξ c d (b ++ [j]) ω - μ)
      * (Ry mk X ξ c d (b ++ [j']) ω - μ) ∂P = 0 := by
    intro j j' hjj
    have hm1 := Ry_meas hgw (b ++ [j])
    have hm2 := Ry_meas hgw (b ++ [j'])
    have hI := indepFun_sgK hgw (hm1.sub_const μ) (hm2.sub_const μ) (disj_KX_children b hjj)
    have := hI.integral_mul_eq_mul_integral
      ((Ry_meas' hgw _).sub_const _).aestronglyMeasurable
      ((Ry_meas' hgw _).sub_const _).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, h0 j, zero_mul]
  have hint : Integrable (fun ω => (c + d) ^ 2 * (Ry mk X ξ c d b ω - M0) ^ 2) P :=
    intg_of_bdd ((((Ry_meas' hgw b).sub_const M0).pow_const 2).const_mul _)
      ((c + d) ^ 2 * (d⁻¹ + |M0|) ^ 2) (fun ω => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (c + d)), abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (Ry_bound hgw b ω) le_rfl)) 2) (sq_nonneg _))
  rw [← integral_const_mul, integral_congr_ae (ae_of_all _ e)]
  refine indep_fubini (XV_indep hgw b) (hgw.measurable_X b) (Vry_meas' hgw b) hF
    (hint.congr (ae_of_all _ e)) hg (fun a => ?_)
  have e2 : ∀ ω, (gf ξ a + ∑ j ∈ Finset.range (mk.N a), mk.C a j * Ry mk X ξ c d (b ++ [j]) ω
        - (c + d) * M0) ^ 2
      = ((gf ξ a + μ * ∑ j ∈ Finset.range (mk.N a), mk.C a j - (c + d) * M0)
        + ∑ j ∈ Finset.range (mk.N a), mk.C a j * (Ry mk X ξ c d (b ++ [j]) ω - μ)) ^ 2 := by
    intro ω
    congr 1
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have : ∀ j, μ * mk.C a j = mk.C a j * μ := fun j => mul_comm _ _
    simp only [this]; ring
  refine (integral_congr_ae (ae_of_all _ e2)).trans ?_
  exact sq_expand (Finset.range (mk.N a)) _ (fun j => mk.C a j)
    (fun j ω => Ry mk X ξ c d (b ++ [j]) ω - μ) B hB0
    (fun j => (Ry_meas' hgw _).sub_const _) hDB h0 hind

set_option maxHeartbeats 1000000 in
lemma ry_var_child [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (μ : ℝ)
    (hμ : μ = (∫ ω, gf ξ (X [0] ω) ∂P) / (c + d - rho1 P mk X)) (b : Label) (hb : b ≠ []) :
    ∫ ω, (Ry mk X ξ c d b ω - μ) ^ 2 ∂P
      = (∫ ω, (gf ξ (X [0] ω) + μ * sumC mk X [0] ω - (c + d) * μ) ^ 2 ∂P)
        / ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X) := by
  have hmc : ∀ b' : Label, b' ≠ [] → ∫ ω, Ry mk X ξ c d b' ω ∂P = μ := fun b' hb' => by
    rw [hμ]; exact ry_mean_child hgw b' hb'
  set A1 := ∫ ω, (gf ξ (X [0] ω) + μ * sumC mk X [0] ω - (c + d) * μ) ^ 2 ∂P with hA1
  set ρ2 := DirectedOpinion.NoMemory.rho2 P mk X with hρ2
  have hd := hgw.d_pos
  have hc0 := hgw.c_nonneg
  obtain ⟨h20, h2c⟩ := rho2_le hgw
  have hCD : 0 < c + d := by linarith
  have hden : 0 < (c + d) ^ 2 - ρ2 := by nlinarith
  set σ := A1 / ((c + d) ^ 2 - ρ2) with hσ
  have hfix : (c + d) ^ 2 * σ = A1 + ρ2 * σ := by rw [hσ]; field_simp; ring
  set r := (c / (c + d)) ^ 2 with hr
  have hr0 : 0 ≤ r := sq_nonneg _
  have hr1 : r < 1 := by
    have h1 : c / (c + d) < 1 := (div_lt_one hCD).2 (by linarith)
    have h0 : 0 ≤ c / (c + d) := div_nonneg hc0 hCD.le
    rw [hr]; nlinarith
  set K := (d⁻¹ + |μ|) ^ 2 + |σ| with hK
  have hK0 : 0 ≤ K := by positivity
  have claim : ∀ k : ℕ, ∀ b : Label, b ≠ [] →
      |∫ ω, (Ry mk X ξ c d b ω - μ) ^ 2 ∂P - σ| ≤ r ^ k * K := by
    intro k
    induction k with
    | zero =>
      intro b _
      rw [pow_zero, one_mul]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      exact abs_int_le _ (fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (Ry_bound hgw _ ω) le_rfl)) 2)
    | succ k ih =>
      intro b hb
      have hf := ry_var_formula hgw b μ μ (fun j => hmc _ (by simp))
      set v : ℕ → ℝ := fun j => ∫ ω', (Ry mk X ξ c d (b ++ [j]) ω' - μ) ^ 2 ∂P with hv
      have he : ∀ j, |v j - σ| ≤ r ^ k * K := fun j => ih (b ++ [j]) (by simp)
      have hrk : 0 ≤ r ^ k * K := mul_nonneg (pow_nonneg hr0 k) hK0
      have hXm := hgw.measurable_X b
      have hSm : Measurable (fun x : M => ∑ j ∈ Finset.range (mk.N x), mk.C x j) :=
        meas_rangeSum _ _ mk.measurable_N (fun j => mk.measurable_C j)
      have hφ : Measurable (fun x : M =>
          (gf ξ x + μ * ∑ j ∈ Finset.range (mk.N x), mk.C x j - (c + d) * μ) ^ 2) :=
        (((gf_meas hgw).add (hSm.const_mul μ)).sub_const _).pow_const 2
      have hA : ∫ ω, (gf ξ (X b ω) + μ * sumC mk X b ω - (c + d) * μ) ^ 2 ∂P = A1 :=
        X_int hgw hb _ hφ
      have hS2 : ∫ ω, sumC2 mk X b ω ∂P = ρ2 :=
        X_int hgw hb (fun x => ∑ j ∈ Finset.range (mk.N x), mk.C x j ^ 2)
          (meas_rangeSum _ _ mk.measurable_N (fun j => (mk.measurable_C j).pow_const 2))
      have iA : Integrable (fun ω => (gf ξ (X b ω) + μ * sumC mk X b ω - (c + d) * μ) ^ 2) P :=
        intg_of_bdd (hφ.comp hXm) ((1 + |μ| * c + |(c + d) * μ|) ^ 2) (fun ω => by
          rw [abs_pow]
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (gf_bound hgw _) ?_)) le_rfl)
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (sumC_le hgw b ω) (abs_nonneg _))
      have iI : Integrable (fun ω => ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j ^ 2 * (v j - σ)) P :=
        intg_of_bdd (meas_rangeSum _ _ (mk.measurable_N.comp hXm)
          (fun j => (((mk.measurable_C j).comp hXm).pow_const 2).mul_const _)) (c ^ 2 * (r ^ k * K))
          (fun ω => wabs _ _ _ _ _ (fun j => sq_nonneg _) (wsum2_le_sq hgw _) hrk he)
      have hS2m : Measurable (sumC2 mk X b) :=
        meas_rangeSum (fun ω => mk.N (X b ω)) (fun j ω => mk.C (X b ω) j ^ 2)
          (mk.measurable_N.comp hXm) (fun j => ((mk.measurable_C j).comp hXm).pow_const 2)
      have iS : Integrable (fun ω => σ * sumC2 mk X b ω) P :=
        (intg_of_bdd hS2m c (fun ω => by
            unfold sumC2
            rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
            exact (wsum2_le_sq hgw _).trans (by nlinarith [hgw.c_lt_one]))).const_mul _
      have e : ∀ ω, (gf ξ (X b ω) + μ * sumC mk X b ω - (c + d) * μ) ^ 2
          + ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2 * v j
          = (gf ξ (X b ω) + μ * sumC mk X b ω - (c + d) * μ) ^ 2
            + (∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2 * (v j - σ)
              + σ * sumC2 mk X b ω) := by
        intro ω
        simp only [sumC2, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        have : ∀ j, σ * mk.C (X b ω) j ^ 2 = mk.C (X b ω) j ^ 2 * σ := fun j => mul_comm _ _
        simp only [this]; ring
      have iIS : Integrable (fun ω => ∑ j ∈ Finset.range (mk.N (X b ω)),
          mk.C (X b ω) j ^ 2 * (v j - σ) + σ * sumC2 mk X b ω) P := iI.add iS
      rw [integral_congr_ae (ae_of_all _ e), integral_add iA iIS, integral_add iI iS,
        integral_const_mul, hA, hS2] at hf
      set I := ∫ ω, ∑ j ∈ Finset.range (mk.N (X b ω)), mk.C (X b ω) j ^ 2 * (v j - σ) ∂P
        with hI
      have hIb : |I| ≤ c ^ 2 * (r ^ k * K) :=
        abs_int_le _ (fun ω => wabs _ _ _ _ _ (fun j => sq_nonneg _) (wsum2_le_sq hgw _) hrk he)
      have hCD2 : 0 < (c + d) ^ 2 := by positivity
      have h2 : ∫ ω, (Ry mk X ξ c d b ω - μ) ^ 2 ∂P - σ = I / (c + d) ^ 2 := by
        field_simp; linarith
      rw [h2, abs_div, abs_of_pos hCD2, div_le_iff₀ hCD2, pow_succ]
      calc |I| ≤ c ^ 2 * (r ^ k * K) := hIb
        _ = r ^ k * r * K * (c + d) ^ 2 := by rw [hr]; field_simp
  have := zero_of_le_pow hr0 hr1 (fun k => claim k b hb)
  linarith

end ry

end T8


namespace T8S
open DirectedOpinion.NoMemory DirectedOpinion.Memory

lemma dsum (F : ℕ × ℕ → ℝ) (h0 : ∀ p, 0 ≤ F p)
    (hs : Summable (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl)) :
    ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl = ∑' a, ∑' b, F (a, b) := by
  set e := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ) with he
  have hfib : ∀ n, ∑' y : Finset.HasAntidiagonal.antidiagonal n, F (e ⟨n, y⟩)
      = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl := by
    intro n; rw [tsum_fintype]; exact Finset.sum_coe_sort _ _
  have hsig : Summable (fun x => F (e x)) := by
    rw [summable_sigma_of_nonneg (fun x => h0 _)]
    refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
    simp_rw [hfib]; exact hs
  have hF : Summable F := e.summable_iff.mp hsig
  rw [← hF.tsum_prod, ← e.tsum_eq F]
  rw [hsig.tsum_sigma' (fun n => (hasSum_fintype _).summable)]
  simp_rw [hfib]

lemma fiber_eq (c d ρ : ℝ) (t n : ℕ) :
    ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (((kl.2 + kl.1 + t).choose kl.2 : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * kl.2) * ρ ^ kl.1
      = ∑ k ∈ Finset.range (n + 1), aCoef c d (k + t) (n + t) ^ 2 * ρ ^ k := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e1 : n - k + k + t = n + t := by omega
  have e2 : n + t - (k + t) = n - k := by omega
  simp only [aCoef, e1, e2]
  rw [Nat.choose_symm_of_eq_add (by omega : n + t = (n - k) + (k + t))]
  rw [mul_pow, ← pow_mul, mul_comm (n - k) 2]

lemma fiber0_le (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hcd : c + d ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ c ^ 2) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), aCoef c d k n ^ 2 * ρ ^ k ≤ ((1 - d) ^ 2) ^ n := by
  have hl : 0 ≤ 1 - c - d := by linarith
  calc ∑ k ∈ Finset.range (n + 1), aCoef c d k n ^ 2 * ρ ^ k
      ≤ ∑ k ∈ Finset.range (n + 1), (c ^ k * (1 - c - d) ^ (n - k) * (n.choose k : ℝ)) ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have : ρ ^ k ≤ (c ^ k) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]; exact pow_le_pow_left₀ hρ0 hρ k
        calc aCoef c d k n ^ 2 * ρ ^ k ≤ aCoef c d k n ^ 2 * (c ^ k) ^ 2 :=
              mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = _ := by unfold aCoef; ring
    _ ≤ (∑ k ∈ Finset.range (n + 1), c ^ k * (1 - c - d) ^ (n - k) * (n.choose k : ℝ)) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => by positivity)
    _ = ((1 - d) ^ 2) ^ n := by
        rw [← add_pow, ← pow_mul, mul_comm, pow_mul]; ring_nf

lemma fiber1_le (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hcd : c + d ≤ 1) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ c ^ 2) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), aCoef c d (k + 1) (n + 1) ^ 2 * ρ ^ k
      ≤ ((n : ℝ) + 1) ^ 2 * ((1 - d) ^ 2) ^ n := by
  have hl : 0 ≤ 1 - c - d := by linarith
  calc ∑ k ∈ Finset.range (n + 1), aCoef c d (k + 1) (n + 1) ^ 2 * ρ ^ k
      ≤ ∑ k ∈ Finset.range (n + 1), ((n : ℝ) + 1) ^ 2 * (aCoef c d k n ^ 2 * ρ ^ k) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hch : ((n + 1).choose (k + 1) : ℝ) ≤ ((n : ℝ) + 1) * (n.choose k : ℝ) := by
          have h := Nat.add_one_mul_choose_eq n k
          have h2 : (n + 1).choose (k + 1) ≤ (n + 1) * n.choose k := by
            rw [h]; exact Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
          exact_mod_cast h2
        have e2 : n + 1 - (k + 1) = n - k := by omega
        unfold aCoef; rw [e2]
        have hp : 0 ≤ ((1 - c - d) ^ (n - k)) ^ 2 * ρ ^ k := by positivity
        have hsq : ((n + 1).choose (k + 1) : ℝ) ^ 2 ≤ (((n : ℝ) + 1) * (n.choose k : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hch 2
        nlinarith [mul_le_mul_of_nonneg_right hsq hp]
    _ = ((n : ℝ) + 1) ^ 2 * ∑ k ∈ Finset.range (n + 1), aCoef c d k n ^ 2 * ρ ^ k := by
        rw [Finset.mul_sum]
    _ ≤ ((n : ℝ) + 1) ^ 2 * ((1 - d) ^ 2) ^ n :=
        mul_le_mul_of_nonneg_left (fiber0_le c d ρ hc hd hcd hρ0 hρ n) (by positivity)

lemma q_lt (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) : 0 ≤ (1 - d) ^ 2 ∧ (1 - d) ^ 2 < 1 := by
  constructor
  · positivity
  · nlinarith

lemma ser_summ (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c ^ 2) (t : ℕ) (ht : t ≤ 1) :
    Summable (fun n => ∑ k ∈ Finset.range (n + 1), aCoef c d (k + t) (n + t) ^ 2 * ρ ^ k) := by
  have hl : 0 ≤ 1 - c - d := by linarith
  obtain ⟨hq0, hq1⟩ := q_lt d hd hd1
  have hg : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * ((1 - d) ^ 2) ^ n) := by
    have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 1 + (n : ℝ) ^ 0)
        * ((1 - d) ^ 2) ^ n) := by
      have a2 := summable_pow_mul_geometric_of_norm_lt_one 2 (r := (1 - d) ^ 2)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
      have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1 - d) ^ 2)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
      have a0 := summable_pow_mul_geometric_of_norm_lt_one 0 (r := (1 - d) ^ 2)
        (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
      simp_rw [add_mul, mul_assoc]
      exact (a2.add (a1.mul_left 2)).add a0
    refine h1.congr (fun n => ?_); ring
  refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg (fun k _ => by positivity))
    (fun n => ?_) hg
  interval_cases t
  · simpa using (fiber0_le c d ρ hc hd hcd hρ0 hρ n).trans
      (le_mul_of_one_le_left (by positivity) (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
  · exact fiber1_le c d ρ hc hd hcd hρ0 hρ n

lemma ser_t (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c ^ 2) (t : ℕ) (ht : t ≤ 1) :
    ∑' n, ∑ k ∈ Finset.range (n + 1), aCoef c d (k + t) (n + t) ^ 2 * ρ ^ k
      = ∑' a, ρ ^ a * ∑' b, (((b + (a + t)).choose b : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * b) := by
  have hl : 0 ≤ 1 - c - d := by linarith
  obtain ⟨hq0, hq1⟩ := q_lt d hd hd1
  set F : ℕ × ℕ → ℝ := fun kl =>
    (((kl.2 + kl.1 + t).choose kl.2 : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * kl.2) * ρ ^ kl.1 with hFd
  have h0 : ∀ p, 0 ≤ F p := fun p => by simp only [hFd]; positivity
  have hfe := fun n => fiber_eq c d ρ t n
  have hs : Summable (fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, F kl) := by
    simp_rw [hFd, hfe]; exact ser_summ c d ρ hc hd hd1 hcd hρ0 hρ t ht
  have := dsum F h0 hs
  simp_rw [hFd, hfe] at this
  rw [this]
  congr 1; funext a
  rw [← tsum_mul_left]
  congr 1; funext b
  rw [show b + a + t = b + (a + t) by ring]; ring

/-- `((c+d)^(2(m+1)))⁻¹ * pT c d m` is the inner series. -/
lemma pT_inner (c d : ℝ) (hcd : 0 < c + d) (m : ℕ) :
    ((c + d) ^ (2 * (m + 1)))⁻¹ * pT c d m
      = ∑' b, (((b + m).choose b : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * b) := by
  unfold pT
  rw [tsum_mul_right, mul_comm, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]

lemma geom_inner (ρ : ℝ) (hρ : ρ < 1) (g : ℕ → ℝ) :
    1 / (1 - ρ) * geomExp ρ g = ∑' k, ρ ^ k * g k := by
  unfold geomExp
  have : (fun k => ρ ^ k * (1 - ρ) * g k) = fun k => (1 - ρ) * (ρ ^ k * g k) := by
    funext k; ring
  rw [this, tsum_mul_left, ← mul_assoc, one_div, inv_mul_cancel₀ (by linarith), one_mul]

lemma lam_geom (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hcd : c + d ≤ 1) :
    ∑' s : ℕ, aCoef c d 0 s ^ 2 = 1 / (1 - (1 - c - d) ^ 2) := by
  have hl : 0 ≤ 1 - c - d := by linarith
  have h1 : (1 - c - d) ^ 2 < 1 := by nlinarith
  have : (fun s : ℕ => aCoef c d 0 s ^ 2) = fun s => ((1 - c - d) ^ 2) ^ s := by
    funext s; unfold aCoef; simp [← pow_mul, mul_comm]
  rw [this, tsum_geometric_of_lt_one (by positivity) h1, one_div]

lemma ser0 (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c ^ 2) :
    ∑' n, ∑ k ∈ Finset.range (n + 1), aCoef c d k n ^ 2 * ρ ^ k
      = ∑' a, ρ ^ a * ∑' b, (((b + a).choose b : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * b) := by
  simpa using ser_t c d ρ hc hd hd1 hcd hρ0 hρ 0 (by norm_num)

lemma ser1 (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c ^ 2) :
    ∑' s, ∑ l ∈ Finset.range s, aCoef c d (l + 1) s ^ 2 * ρ ^ l
      = ∑' a, ρ ^ a * ∑' b, (((b + (a + 1)).choose b : ℕ) : ℝ) ^ 2 * (1 - c - d) ^ (2 * b) := by
  have h1 := ser_summ c d ρ hc hd hd1 hcd hρ0 hρ 1 le_rfl
  have hS : Summable (fun s => ∑ l ∈ Finset.range s, aCoef c d (l + 1) s ^ 2 * ρ ^ l) :=
    (summable_nat_add_iff 1).mp h1
  rw [hS.tsum_eq_zero_add]
  simpa using ser_t c d ρ hc hd hd1 hcd hρ0 hρ 1 le_rfl

lemma ser1_summ (c d ρ : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hd1 : d ≤ 1) (hcd : c + d ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ c ^ 2) :
    Summable (fun s => ∑ l ∈ Finset.range s, aCoef c d (l + 1) s ^ 2 * ρ ^ l) :=
  (summable_nat_add_iff 1).mp (ser_summ c d ρ hc hd hd1 hcd hρ0 hρ 1 le_rfl)

lemma lam_summ (c d : ℝ) (hc : 0 ≤ c) (hd : 0 < d) (hcd : c + d ≤ 1) :
    Summable (fun s : ℕ => aCoef c d 0 s ^ 2) := by
  have hl : 0 ≤ 1 - c - d := by linarith
  have h1 : (1 - c - d) ^ 2 < 1 := by nlinarith
  have : (fun s : ℕ => aCoef c d 0 s ^ 2) = fun s => ((1 - c - d) ^ 2) ^ s := by
    funext s; unfold aCoef; simp [← pow_mul, mul_comm]
  rw [this]; exact summable_geometric_of_lt_one (by positivity) h1

end T8S


namespace T8F
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


/-- E[F(Y,V) | Y] = g(Y) when Y ⟂ V and g a = E F(a,V). -/
lemma condexp_ident {Ω α β : Type*} {mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → α} {V : Ω → β}
    (hYV : IndepFun Y V P) (hY : Measurable Y) (hV : Measurable V)
    {F : α × β → ℝ} (hF : Measurable F) (B : ℝ) (hB : ∀ p, |F p| ≤ B)
    {g : α → ℝ} (hg : Measurable g) (hgB : ∀ a, |g a| ≤ B)
    (hFg : ∀ a, ∫ ω, F (a, V ω) ∂P = g a) :
    (fun ω => g (Y ω)) =ᵐ[P] P[fun ω => F (Y ω, V ω) | MeasurableSpace.comap Y mα] := by
  have hm : MeasurableSpace.comap Y mα ≤ mΩ := hY.comap_le
  have hFm : Measurable (fun ω => F (Y ω, V ω)) := hF.comp (hY.prodMk hV)
  have hgm : Measurable (fun ω => g (Y ω)) := hg.comp hY
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (intg_of_bdd hFm B (fun ω => hB _))
    (fun s _ _ => (intg_of_bdd hgm B (fun ω => hgB _)).integrableOn) ?_
    ((hg.comp (comap_measurable Y)).aestronglyMeasurable)
  rintro s ⟨A, hA, rfl⟩ _
  have hYm : MeasurableSet (Y ⁻¹' A) := hY hA
  rw [← integral_indicator hYm, ← integral_indicator hYm]
  set G : α × β → ℝ := fun p => A.indicator (fun _ => (1 : ℝ)) p.1 * F p with hG
  have hGm : Measurable G :=
    (((measurable_const.indicator hA).comp measurable_fst).mul hF)
  have e1 : (Y ⁻¹' A).indicator (fun ω => F (Y ω, V ω)) = fun ω => G (Y ω, V ω) := by
    funext ω; by_cases h : Y ω ∈ A <;> simp [hG, Set.indicator, h]
  have e2 : (Y ⁻¹' A).indicator (fun ω => g (Y ω))
      = fun ω => (fun a => A.indicator (fun _ => (1 : ℝ)) a * g a) (Y ω) := by
    funext ω; by_cases h : Y ω ∈ A <;> simp [Set.indicator, h]
  rw [e1, e2]
  symm
  refine indep_fubini hYV hY hV hGm ?_ ((measurable_const.indicator hA).mul hg) ?_
  · refine intg_of_bdd (hGm.comp (hY.prodMk hV)) B (fun ω => ?_)
    simp only [hG]
    by_cases h : Y ω ∈ A <;> simp [Set.indicator, h, hB, (abs_nonneg _).trans (hB (Y ω, V ω))]
  · intro a
    simp only [hG]
    rw [integral_const_mul, hFg a]

/-- variance split for orthogonal centred noise. -/
lemma var_split {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Ω → ℝ} (hA : Measurable A) (hB : Measurable B) (K : ℝ) (hAK : ∀ ω, |A ω| ≤ K)
    (hBK : ∀ ω, |B ω| ≤ K) (hB0 : ∫ ω, B ω ∂P = 0) (hAB : ∫ ω, A ω * B ω ∂P = 0) (m : ℝ) :
    ∫ ω, (A ω + B ω - m) ^ 2 ∂P = ∫ ω, (A ω - m) ^ 2 ∂P + ∫ ω, B ω ^ 2 ∂P := by
  have iA : Integrable A P := intg_of_bdd hA K hAK
  have iB : Integrable B P := intg_of_bdd hB K hBK
  have iAB : Integrable (fun ω => A ω * B ω) P :=
    intg_of_bdd (hA.mul hB) (K * K) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hAK ω) (hBK ω) (abs_nonneg _) ((abs_nonneg _).trans (hAK ω)))
  have iA2 : Integrable (fun ω => (A ω - m) ^ 2) P :=
    intg_of_bdd ((hA.sub measurable_const).pow_const 2) ((K + |m|) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _)
        ((abs_sub _ _).trans (add_le_add (hAK ω) le_rfl)) 2)
  have iB2 : Integrable (fun ω => B ω ^ 2) P :=
    intg_of_bdd (hB.pow_const 2) (K ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBK ω) 2)
  have e : (fun ω => (A ω + B ω - m) ^ 2)
      = fun ω => ((A ω - m) ^ 2 + B ω ^ 2) + (2 * (A ω * B ω) - 2 * m * B ω) := by
    funext ω; ring
  have j1 : Integrable (fun ω => (A ω - m) ^ 2 + B ω ^ 2) P := iA2.add iB2
  have j2 : Integrable (fun ω => 2 * (A ω * B ω)) P := iAB.const_mul 2
  have j3 : Integrable (fun ω => 2 * m * B ω) P := iB.const_mul (2 * m)
  have j4 : Integrable (fun ω => 2 * (A ω * B ω) - 2 * m * B ω) P := j2.sub j3
  rw [e, integral_add j1 j4, integral_add iA2 iB2, integral_sub j2 j3,
    integral_const_mul, integral_const_mul, hAB, hB0]
  ring

/-- expansion of E[((g-a) + m(S-b))²]. -/
lemma quad_int {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {g S : Ω → ℝ} (hg : Measurable g) (hS : Measurable S) (K : ℝ) (hgK : ∀ ω, |g ω| ≤ K)
    (hSK : ∀ ω, |S ω| ≤ K) (a b m : ℝ) :
    ∫ ω, ((g ω - a) + m * (S ω - b)) ^ 2 ∂P
      = ∫ ω, (g ω - a) ^ 2 ∂P + m ^ 2 * ∫ ω, (S ω - b) ^ 2 ∂P
        + 2 * m * ∫ ω, (S ω - b) * (g ω - a) ∂P := by
  have bd : ∀ (f : Ω → ℝ) (hf : Measurable f) (hfK : ∀ ω, |f ω| ≤ K) (x : ℝ),
      Measurable (fun ω => f ω - x) ∧ ∀ ω, |f ω - x| ≤ K + |x| := fun f hf hfK x =>
    ⟨hf.sub measurable_const, fun ω => (abs_sub _ _).trans (add_le_add (hfK ω) le_rfl)⟩
  obtain ⟨mg, bg⟩ := bd g hg hgK a
  obtain ⟨mS, bS⟩ := bd S hS hSK b
  have i1 : Integrable (fun ω => (g ω - a) ^ 2) P :=
    intg_of_bdd (mg.pow_const 2) ((K + |a|) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (bg ω) 2)
  have i2 : Integrable (fun ω => (S ω - b) ^ 2) P :=
    intg_of_bdd (mS.pow_const 2) ((K + |b|) ^ 2) (fun ω => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (bS ω) 2)
  have i3 : Integrable (fun ω => (S ω - b) * (g ω - a)) P :=
    intg_of_bdd (mS.mul mg) ((K + |b|) * (K + |a|)) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (bS ω) (bg ω) (abs_nonneg _)
        ((abs_nonneg _).trans (bS ω)))
  have e : (fun ω => ((g ω - a) + m * (S ω - b)) ^ 2)
      = fun ω => ((g ω - a) ^ 2 + m ^ 2 * (S ω - b) ^ 2) + 2 * m * ((S ω - b) * (g ω - a)) := by
    funext ω; ring
  have j2 : Integrable (fun ω => m ^ 2 * (S ω - b) ^ 2) P := i2.const_mul _
  have j1 : Integrable (fun ω => (g ω - a) ^ 2 + m ^ 2 * (S ω - b) ^ 2) P := i1.add j2
  have j3 : Integrable (fun ω => 2 * m * ((S ω - b) * (g ω - a))) P := i3.const_mul _
  rw [e, integral_add j1 j3, integral_add i1 j2, integral_const_mul, integral_const_mul]

end T8F


namespace T8A

lemma final_alg {c d ρ1 ρ1s ρ2 ρ2s EW0 EW1 VS0 VS1 VY0 VY1 Cv0 Cv1 EV0 EV1 G1 G2 ERs ER VRs VR
    A0 σ2 : ℝ}
    (hcd : 0 < c + d) (h1 : 0 < c + d - ρ1) (h2 : 0 < (c + d) ^ 2 - ρ2)
    (hERs : (c + d) * ERs = EW0 + EW1 / (c + d - ρ1) * ρ1s)
    (hER : ER = EW1 / (c + d - ρ1))
    (hσ : σ2 = (VY1 + (EW1 / (c + d - ρ1)) ^ 2 * VS1 + 2 * (EW1 / (c + d - ρ1)) * Cv1)
      / ((c + d) ^ 2 - ρ2))
    (hA0 : (c + d) ^ 2 * A0 = VY0 + (EW1 / (c + d - ρ1)) ^ 2 * VS0
      + 2 * (EW1 / (c + d - ρ1)) * Cv0 + ρ2s * σ2)
    (hVRs : VRs = A0 + (EV0 * (1 / (1 - (1 - c - d) ^ 2)) + ρ2s * EV1 * (1 / (1 - ρ2)) * G2))
    (hVR : VR = σ2 + EV1 * (1 / (1 - ρ2)) * G1) :
    (ERs = 1 / (c + d) * EW0 + ρ1s / ((c + d - ρ1) * (c + d)) * EW1) ∧
    (ER = EW1 / (c + d - ρ1)) ∧
    VRs
      = VS0 * EW1 ^ 2 * (1 / ((c + d) ^ 2 * (c + d - ρ1) ^ 2))
        + VY0 * (1 / (c + d) ^ 2)
        + 2 * Cv0 * EW1 * (1 / ((c + d) ^ 2 * (c + d - ρ1)))
        + EV0 * (1 / (1 - (1 - c - d) ^ 2))
        + ρ2s * VS1 * EW1 ^ 2
          * (1 / ((c + d) ^ 2 * (c + d - ρ1) ^ 2 * ((c + d) ^ 2 - ρ2)))
        + ρ2s * EV1 * (1 / (1 - ρ2)) * G2
        + ρ2s * VY1 * (1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ2)))
        + 2 * ρ2s * Cv1 * EW1
          * (1 / ((c + d) ^ 2 * (c + d - ρ1) * ((c + d) ^ 2 - ρ2))) ∧
    VR
      = VS1 * EW1 ^ 2 * (1 / (((c + d) - ρ1) ^ 2 * ((c + d) ^ 2 - ρ2)))
        + EV1 * (1 / (1 - ρ2)) * G1
        + VY1 * (1 / ((c + d) ^ 2 - ρ2))
        + 2 * Cv1 * EW1 * (1 / ((c + d - ρ1) * ((c + d) ^ 2 - ρ2))) := by
  have a0 : c + d ≠ 0 := hcd.ne'
  have a1 : c + d - ρ1 ≠ 0 := h1.ne'
  have a2 : (c + d) ^ 2 - ρ2 ≠ 0 := h2.ne'
  have hA0' : A0 = (VY0 + (EW1 / (c + d - ρ1)) ^ 2 * VS0
      + 2 * (EW1 / (c + d - ρ1)) * Cv0 + ρ2s * σ2) / (c + d) ^ 2 := by
    rw [← hA0]; field_simp
  have hERs' : ERs = (EW0 + EW1 / (c + d - ρ1) * ρ1s) / (c + d) := by
    rw [← hERs]; field_simp
  refine ⟨?_, hER, ?_, ?_⟩
  · rw [hERs']; field_simp
  · rw [hVRs, hA0', hσ]
    generalize EV0 * (1 / (1 - (1 - c - d) ^ 2)) = T0
    generalize ρ2s * EV1 * (1 / (1 - ρ2)) * G2 = T2
    field_simp; ring
  · rw [hVR, hσ]
    generalize EV1 * (1 / (1 - ρ2)) * G1 = T1
    field_simp; ring

end T8A

namespace T8
open DirectedOpinion.NoMemory DirectedOpinion.Memory

section glue
variable {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
variable {P : Measure Ω} {mk : MarkFns M} {X : Label → Ω → M} {U : Label → ℕ → Ω → ℝ}
  {ξ : M → ℝ → ℝ} {c d : ℝ}

lemma Y_ae [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    (fun ω => gf ξ (X b ω)) =ᵐ[P] condMeanSig P X (Z X U ξ) b := by
  unfold condMeanSig
  exact T8F.condexp_ident (XU_indep hgw b 0) (hgw.measurable_X b) (hgw.measurable_U b 0)
    hgw.measurable_ζ 1 (fun p => abs_le.2 ⟨(hgw.ζ_mem p.1 p.2).1, (hgw.ζ_mem p.1 p.2).2⟩)
    (gf_meas hgw) (gf_bound hgw) (fun a => int_U hgw b 0 a)

lemma EW_eq [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, Z X U ξ b 0 ω ∂P = ∫ ω, gf ξ (X b ω) ∂P := by
  have h := Y_ae hgw b
  unfold condMeanSig at h
  calc ∫ ω, Z X U ξ b 0 ω ∂P
      = ∫ ω, (P[Z X U ξ b 0 | MeasurableSpace.comap (X b) inferInstance]) ω ∂P :=
        (integral_condExp (hgw.measurable_X b).comap_le).symm
    _ = ∫ ω, gf ξ (X b ω) ∂P := (integral_congr_ae h).symm

lemma V_int [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, condVarSig P X (Z X U ξ) b ω ∂P = ∫ ω, Dn X U ξ b 0 ω ^ 2 ∂P := by
  have h := Y_ae hgw b
  unfold condMeanSig at h
  unfold condVarSig condVar
  rw [integral_condExp (hgw.measurable_X b).comap_le]
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  simp only [Pi.pow_apply, Pi.sub_apply, Dn, ← hω]

lemma varY [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    variance (condMeanSig P X (Z X U ξ) b) P
      = ∫ ω, (gf ξ (X b ω) - ∫ ω', gf ξ (X b ω') ∂P) ^ 2 ∂P := by
  rw [← variance_congr (Y_ae hgw b)]
  exact variance_eq_integral ((gf_meas hgw).comp (hgw.measurable_X b)).aemeasurable

lemma covY [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    covariance (sumC mk X b) (condMeanSig P X (Z X U ξ) b) P
      = ∫ ω, (sumC mk X b ω - ∫ ω', sumC mk X b ω' ∂P)
          * (gf ξ (X b ω) - ∫ ω', gf ξ (X b ω') ∂P) ∂P := by
  have h := Y_ae hgw b
  have hi : ∫ ω, condMeanSig P X (Z X U ξ) b ω ∂P = ∫ ω, gf ξ (X b ω) ∂P :=
    (integral_congr_ae h).symm
  unfold covariance
  rw [hi]
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  rw [hω]

lemma varS (hgw : GWModel P mk X U ξ c d) (b : Label) :
    variance (sumC mk X b) P = ∫ ω, (sumC mk X b ω - ∫ ω', sumC mk X b ω' ∂P) ^ 2 ∂P :=
  variance_eq_integral (sumC_meas hgw b).aemeasurable

lemma lim_moments [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (b : Label) :
    ∫ ω, limOpinion mk X (Z X U ξ) c d b ω ∂P = ∫ ω, Ry mk X ξ c d b ω ∂P ∧
    variance (limOpinion mk X (Z X U ξ) c d b) P
      = ∫ ω, (Ry mk X ξ c d b ω - ∫ ω', Ry mk X ξ c d b ω' ∂P) ^ 2 ∂P
        + ∫ ω, Nz mk X U ξ c d b ω ^ 2 ∂P := by
  have e : limOpinion mk X (Z X U ξ) c d b
      = fun ω => Ry mk X ξ c d b ω + Nz mk X U ξ c d b ω := funext (lim_split hgw b)
  have hNi : Integrable (Nz mk X U ξ c d b) P := intg_of_bdd (Nz_meas hgw b) _ (Nz_bound hgw b)
  have hm : ∫ ω, limOpinion mk X (Z X U ξ) c d b ω ∂P = ∫ ω, Ry mk X ξ c d b ω ∂P := by
    rw [e, integral_add (Ry_int hgw b) hNi, Nz_mean hgw b, add_zero]
  refine ⟨hm, ?_⟩
  have hd := hgw.d_pos
  have hdi : 0 < d⁻¹ := inv_pos.2 hd
  have hmeas : AEMeasurable (limOpinion mk X (Z X U ξ) c d b) P := by
    rw [e]; exact ((Ry_meas' hgw b).add (Nz_meas hgw b)).aemeasurable
  rw [variance_eq_integral hmeas, hm, e]
  exact T8F.var_split (Ry_meas' hgw b) (Nz_meas hgw b) (d⁻¹ * 2)
    (fun ω => (Ry_bound hgw b ω).trans (by linarith)) (Nz_bound hgw b) (Nz_mean hgw b)
    (Ry_Nz hgw b) _

lemma rho2_lt_one (hgw : GWModel P mk X U ξ c d) [IsProbabilityMeasure P] :
    DirectedOpinion.NoMemory.rho2 P mk X < 1 := by
  have h := (rho2_le hgw).2
  have h0 := hgw.c_nonneg
  have h1 := hgw.c_lt_one
  nlinarith

lemma nz1 [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) :
    ∫ ω, Nz mk X U ξ c d [0] ω ^ 2 ∂P
      = (∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P) * (1 / (1 - DirectedOpinion.NoMemory.rho2 P mk X))
        * geomExp (DirectedOpinion.NoMemory.rho2 P mk X)
            (fun k => ((c + d) ^ (2 * (k + 1)))⁻¹ * pT c d k) := by
  obtain ⟨h0, h1⟩ := rho2_le hgw
  have hρ1 := rho2_lt_one hgw
  have hcd : 0 < c + d := by linarith [hgw.d_pos, hgw.c_nonneg]
  set EV := ∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P with hEV
  set ρ2 := DirectedOpinion.NoMemory.rho2 P mk X with hρ2
  rw [Nz_sq hgw [0]]
  have e : ∀ s, ∫ ω, Gs mk X U ξ c d [0] s ω ^ 2 ∂P
      = (∑ l ∈ Finset.range (s + 1), aCoef c d l s ^ 2 * ρ2 ^ l) * EV := by
    intro s; rw [Gs_sq hgw [0] s, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Ql_sq hgw s l [0] (by simp)]; ring
  simp_rw [e]
  have hT : ∑' s, ∑ l ∈ Finset.range (s + 1), aCoef c d l s ^ 2 * ρ2 ^ l
      = 1 / (1 - ρ2) * geomExp ρ2 (fun k => ((c + d) ^ (2 * (k + 1)))⁻¹ * pT c d k) := by
    rw [T8S.ser0 c d ρ2 hgw.c_nonneg hgw.d_pos hgw.d_le_one hgw.cd_le_one h0 h1,
      T8S.geom_inner ρ2 hρ1]
    exact tsum_congr (fun k => by rw [T8S.pT_inner c d hcd k])
  rw [tsum_mul_right, hT]; ring

lemma nz0 [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) :
    ∫ ω, Nz mk X U ξ c d [] ω ^ 2 ∂P
      = (∫ ω, Dn X U ξ [] 0 ω ^ 2 ∂P) * (1 / (1 - (1 - c - d) ^ 2))
        + rho2star P mk X * (∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P)
          * (1 / (1 - DirectedOpinion.NoMemory.rho2 P mk X))
          * geomExp (DirectedOpinion.NoMemory.rho2 P mk X)
              (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1)) := by
  obtain ⟨h0, h1⟩ := rho2_le hgw
  have hρ1 := rho2_lt_one hgw
  have hcd : 0 < c + d := by linarith [hgw.d_pos, hgw.c_nonneg]
  set EV0 := ∫ ω, Dn X U ξ [] 0 ω ^ 2 ∂P with hEV0
  set EV1 := ∫ ω, Dn X U ξ [0] 0 ω ^ 2 ∂P with hEV1
  set ρ2 := DirectedOpinion.NoMemory.rho2 P mk X with hρ2
  set ρ2s := rho2star P mk X with hρ2s
  rw [Nz_sq hgw []]
  have e : ∀ s, ∫ ω, Gs mk X U ξ c d [] s ω ^ 2 ∂P
      = (ρ2s * EV1) * (∑ l ∈ Finset.range s, aCoef c d (l + 1) s ^ 2 * ρ2 ^ l)
        + EV0 * aCoef c d 0 s ^ 2 := by
    intro s
    rw [Gs_sq hgw [] s, Finset.sum_range_succ', Ql_sq_root0 hgw s, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [Ql_sq_root hgw s l]; ring
    · ring
  simp_rw [e]
  have hT : ∑' s, ∑ l ∈ Finset.range s, aCoef c d (l + 1) s ^ 2 * ρ2 ^ l
      = 1 / (1 - ρ2) * geomExp ρ2 (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1)) := by
    rw [T8S.ser1 c d ρ2 hgw.c_nonneg hgw.d_pos hgw.d_le_one hgw.cd_le_one h0 h1,
      T8S.geom_inner ρ2 hρ1]
    refine tsum_congr (fun k => ?_)
    rw [show 2 * (k + 2) = 2 * (k + 1 + 1) by ring, T8S.pT_inner c d hcd (k + 1)]
  have s1 := (T8S.ser1_summ c d ρ2 hgw.c_nonneg hgw.d_pos hgw.d_le_one hgw.cd_le_one h0 h1).mul_left
    (ρ2s * EV1)
  have s2 := (T8S.lam_summ c d hgw.c_nonneg hgw.d_pos hgw.cd_le_one).mul_left EV0
  rw [s1.tsum_add s2, tsum_mul_left, tsum_mul_left, hT,
    T8S.lam_geom c d hgw.c_nonneg hgw.d_pos hgw.cd_le_one]
  ring

lemma intg_affine_sq [IsProbabilityMeasure P] {g S : Ω → ℝ} (hg : Measurable g)
    (hS : Measurable S) (K : ℝ) (hgK : ∀ ω, |g ω| ≤ K) (hSK : ∀ ω, |S ω| ≤ K) (a b m : ℝ) :
    Integrable (fun ω => ((g ω - a) + m * (S ω - b)) ^ 2) P :=
  intg_of_bdd (((hg.sub measurable_const).add ((hS.sub measurable_const).const_mul m)).pow_const 2)
    ((K + |a| + |m| * (K + |b|)) ^ 2) (fun ω => by
      rw [abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |g ω - a + m * (S ω - b)| ≤ |g ω - a| + |m * (S ω - b)| := abs_add_le _ _
        _ ≤ (K + |a|) + |m| * (K + |b|) := by
          refine add_le_add ((abs_sub _ _).trans (add_le_add (hgK ω) le_rfl)) ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hSK ω) le_rfl))
            (abs_nonneg _)
        _ = _ := by ring)

lemma ry_child [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (μ : ℝ)
    (hμ : μ = (∫ ω, gf ξ (X [0] ω) ∂P) / (c + d - rho1 P mk X)) :
    ∫ ω, (Ry mk X ξ c d [0] ω - μ) ^ 2 ∂P
      = (variance (condMeanSig P X (Z X U ξ) [0]) P + μ ^ 2 * variance (sumC mk X [0]) P
          + 2 * μ * covariance (sumC mk X [0]) (condMeanSig P X (Z X U ξ) [0]) P)
        / ((c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X) := by
  rw [ry_var_child hgw μ hμ [0] (by simp), varY hgw [0], covY hgw [0], varS hgw [0]]
  congr 1
  have hne : c + d - rho1 P mk X ≠ 0 := by
    have := (rho1_le hgw).2; have := hgw.d_pos; exact ne_of_gt (by linarith)
  have hμ' : (c + d) * μ = (∫ ω, gf ξ (X [0] ω) ∂P) + μ * rho1 P mk X := by
    rw [hμ]; field_simp; ring
  have hr : rho1 P mk X = ∫ ω, sumC mk X [0] ω ∂P := rfl
  have e : ∀ ω, gf ξ (X [0] ω) + μ * sumC mk X [0] ω - (c + d) * μ
      = (gf ξ (X [0] ω) - ∫ ω', gf ξ (X [0] ω') ∂P)
        + μ * (sumC mk X [0] ω - ∫ ω', sumC mk X [0] ω' ∂P) := fun ω => by
    rw [← hr]; linear_combination (-1 : ℝ) * hμ'
  simp_rw [e]
  exact T8F.quad_int ((gf_meas hgw).comp (hgw.measurable_X [0])) (sumC_meas hgw [0]) (1 + c)
    (fun ω => (gf_bound hgw _).trans (by linarith [hgw.c_nonneg]))
    (fun ω => (sumC_le hgw [0] ω).trans (by linarith)) _ _ _

set_option maxHeartbeats 1000000 in
lemma ry_root [IsProbabilityMeasure P] (hgw : GWModel P mk X U ξ c d) (μ : ℝ)
    (hμ : μ = (∫ ω, gf ξ (X [0] ω) ∂P) / (c + d - rho1 P mk X)) :
    (c + d) * ∫ ω, Ry mk X ξ c d [] ω ∂P = (∫ ω, gf ξ (X [] ω) ∂P) + μ * rho1star P mk X ∧
    (c + d) ^ 2 * ∫ ω, (Ry mk X ξ c d [] ω - ∫ ω', Ry mk X ξ c d [] ω' ∂P) ^ 2 ∂P
      = variance (condMeanSig P X (Z X U ξ) []) P + μ ^ 2 * variance (sumC mk X []) P
        + 2 * μ * covariance (sumC mk X []) (condMeanSig P X (Z X U ξ) []) P
        + rho2star P mk X * ∫ ω, (Ry mk X ξ c d [0] ω - μ) ^ 2 ∂P := by
  have hmc : ∀ j, ∫ ω, Ry mk X ξ c d ([] ++ [j]) ω ∂P = μ := fun j => by
    rw [hμ]; exact ry_mean_child hgw _ (by simp)
  have hgi : Integrable (fun ω => gf ξ (X [] ω)) P :=
    intg_of_bdd ((gf_meas hgw).comp (hgw.measurable_X [])) 1 (fun ω => gf_bound hgw _)
  have hSi : Integrable (sumC mk X []) P := intg_of_bdd (sumC_meas hgw []) c (sumC_le hgw [])
  have hmean : (c + d) * ∫ ω, Ry mk X ξ c d [] ω ∂P
      = (∫ ω, gf ξ (X [] ω) ∂P) + μ * rho1star P mk X := by
    rw [ry_mean_formula hgw []]
    simp only [hmc]
    have e : ∀ ω, gf ξ (X [] ω) + ∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j * μ
        = gf ξ (X [] ω) + μ * sumC mk X [] ω := fun ω => by
      unfold sumC; rw [← Finset.sum_mul]; ring
    simp_rw [e]
    have hSi' : Integrable (fun ω => μ * sumC mk X [] ω) P := hSi.const_mul μ
    rw [integral_add hgi hSi', integral_const_mul]
    rfl
  refine ⟨hmean, ?_⟩
  set M0 := ∫ ω', Ry mk X ξ c d [] ω' ∂P with hM0
  rw [ry_var_formula hgw [] μ M0 hmc]
  have hσ : ∀ j, ∫ ω, (Ry mk X ξ c d ([] ++ [j]) ω - μ) ^ 2 ∂P
      = ∫ ω, (Ry mk X ξ c d [0] ω - μ) ^ 2 ∂P := fun j => by
    rw [ry_var_child hgw μ hμ _ (by simp), ry_var_child hgw μ hμ [0] (by simp)]
  simp only [hσ]
  set σ2 := ∫ ω, (Ry mk X ξ c d [0] ω - μ) ^ 2 ∂P with hσ2
  have hmean' : (c + d) * M0 = (∫ ω, gf ξ (X [] ω) ∂P) + μ * ∫ ω, sumC mk X [] ω ∂P := hmean
  have e : ∀ ω, (gf ξ (X [] ω) + μ * sumC mk X [] ω - (c + d) * M0) ^ 2
        + ∑ j ∈ Finset.range (mk.N (X [] ω)), mk.C (X [] ω) j ^ 2 * σ2
      = ((gf ξ (X [] ω) - ∫ ω', gf ξ (X [] ω') ∂P)
          + μ * (sumC mk X [] ω - ∫ ω', sumC mk X [] ω' ∂P)) ^ 2
        + σ2 * sumC2 mk X [] ω := fun ω => by
    rw [hmean']
    unfold sumC2
    rw [Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [e]
  have hq := intg_affine_sq (P := P) (g := fun ω => gf ξ (X [] ω)) ((gf_meas hgw).comp (hgw.measurable_X []))
    (sumC_meas hgw []) (1 + c) (fun ω => (gf_bound hgw _).trans (by linarith [hgw.c_nonneg]))
    (fun ω => (sumC_le hgw [] ω).trans (by linarith)) (∫ ω', gf ξ (X [] ω') ∂P)
    (∫ ω', sumC mk X [] ω' ∂P) μ
  have hC2m : Measurable (sumC2 mk X []) :=
    meas_rangeSum (fun ω => mk.N (X [] ω)) (fun j ω => mk.C (X [] ω) j ^ 2)
      (mk.measurable_N.comp (hgw.measurable_X []))
      (fun j => ((mk.measurable_C j).comp (hgw.measurable_X [])).pow_const 2)
  have hC2i : Integrable (sumC2 mk X []) P := intg_of_bdd hC2m (c ^ 2) (fun ω => by
    unfold sumC2
    rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    exact wsum2_le_sq hgw _)
  have hC2i' : Integrable (fun ω => σ2 * sumC2 mk X [] ω) P := hC2i.const_mul σ2
  rw [integral_add hq hC2i', integral_const_mul,
    T8F.quad_int (g := fun ω => gf ξ (X [] ω)) ((gf_meas hgw).comp (hgw.measurable_X []))
      (sumC_meas hgw []) (1 + c)
      (fun ω => (gf_bound hgw _).trans (by linarith [hgw.c_nonneg]))
      (fun ω => (sumC_le hgw [] ω).trans (by linarith)) _ _ _,
    varY hgw [], covY hgw [], varS hgw []]
  have hr2 : rho2star P mk X = ∫ ω, sumC2 mk X [] ω ∂P := rfl
  rw [hr2]; ring

end glue

end T8

set_option maxHeartbeats 1000000 in
open MeasureTheory ProbabilityTheory DirectedOpinion.Memory in
theorem solution {Ω M : Type*} [MeasurableSpace Ω] [MeasurableSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (mk : DirectedOpinion.NoMemory.MarkFns M) (X : DirectedOpinion.NoMemory.Label → Ω → M)
    (U : DirectedOpinion.NoMemory.Label → ℕ → Ω → ℝ) (ξ : M → ℝ → ℝ) (c d : ℝ)
    (hGW : DirectedOpinion.NoMemory.GWModel P mk X U ξ c d)
    (hξ : ∀ x u, |ξ x u| ≤ d + c - ∑ j ∈ Finset.range (mk.N x), mk.C x j) :
    let ρ₁s := rho1star P mk X
    let ρ₁ := rho1 P mk X
    let ρ₂s := rho2star P mk X
    let ρ₂ := DirectedOpinion.NoMemory.rho2 P mk X
    let EW0 := ∫ ω, DirectedOpinion.NoMemory.Z X U ξ [] 0 ω ∂P
    let EW1 := ∫ ω, DirectedOpinion.NoMemory.Z X U ξ [0] 0 ω ∂P
    let Y := condMeanSig P X (DirectedOpinion.NoMemory.Z X U ξ)
    let V := condVarSig P X (DirectedOpinion.NoMemory.Z X U ξ)
    let Rstar := limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d []
    let R := limOpinion mk X (DirectedOpinion.NoMemory.Z X U ξ) c d [0]
    (∫ ω, Rstar ω ∂P = 1 / (c + d) * EW0 + ρ₁s / ((c + d - ρ₁) * (c + d)) * EW1) ∧
    (∫ ω, R ω ∂P = EW1 / (c + d - ρ₁)) ∧
    variance Rstar P
      = variance (sumC mk X []) P * EW1 ^ 2 * (1 / ((c + d) ^ 2 * (c + d - ρ₁) ^ 2))
        + variance (Y []) P * (1 / (c + d) ^ 2)
        + 2 * covariance (sumC mk X []) (Y []) P * EW1 * (1 / ((c + d) ^ 2 * (c + d - ρ₁)))
        + (∫ ω, V [] ω ∂P) * (1 / (1 - (1 - c - d) ^ 2))
        + ρ₂s * variance (sumC mk X [0]) P * EW1 ^ 2
          * (1 / ((c + d) ^ 2 * (c + d - ρ₁) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + ρ₂s * (∫ ω, V [0] ω ∂P) * (1 / (1 - ρ₂))
          * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 2)))⁻¹ * pT c d (k + 1))
        + ρ₂s * variance (Y [0]) P * (1 / ((c + d) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + 2 * ρ₂s * covariance (sumC mk X [0]) (Y [0]) P * EW1
          * (1 / ((c + d) ^ 2 * (c + d - ρ₁) * ((c + d) ^ 2 - ρ₂))) ∧
    variance R P
      = variance (sumC mk X [0]) P * EW1 ^ 2 * (1 / (((c + d) - ρ₁) ^ 2 * ((c + d) ^ 2 - ρ₂)))
        + (∫ ω, V [0] ω ∂P) * (1 / (1 - ρ₂))
          * geomExp ρ₂ (fun k => ((c + d) ^ (2 * (k + 1)))⁻¹ * pT c d k)
        + variance (Y [0]) P * (1 / ((c + d) ^ 2 - ρ₂))
        + 2 * covariance (sumC mk X [0]) (Y [0]) P * EW1
          * (1 / ((c + d - ρ₁) * ((c + d) ^ 2 - ρ₂))) := by
  dsimp only
  have hd := hGW.d_pos
  have hc := hGW.c_nonneg
  obtain ⟨r1a, r1b⟩ := T8.rho1_le hGW
  obtain ⟨r2a, r2b⟩ := T8.rho2_le hGW
  have hcd : 0 < c + d := by linarith
  have h1 : 0 < c + d - rho1 P mk X := by linarith
  have h2 : 0 < (c + d) ^ 2 - DirectedOpinion.NoMemory.rho2 P mk X := by nlinarith
  have hEW0 := T8.EW_eq hGW []
  have hEW1 := T8.EW_eq hGW [0]
  have hμ : (∫ ω, DirectedOpinion.NoMemory.Z X U ξ [0] 0 ω ∂P) / (c + d - rho1 P mk X)
      = (∫ ω, T8.gf ξ (X [0] ω) ∂P) / (c + d - rho1 P mk X) := by rw [hEW1]
  obtain ⟨hm0, hv0⟩ := T8.lim_moments hGW []
  obtain ⟨hm1, hv1⟩ := T8.lim_moments hGW [0]
  obtain ⟨hr0, hr0v⟩ := T8.ry_root hGW _ hμ
  have hrc := T8.ry_child hGW _ hμ
  have hn0 := T8.nz0 hGW
  have hn1 := T8.nz1 hGW
  have hV0 := T8.V_int hGW []
  have hV1 := T8.V_int hGW [0]
  refine T8A.final_alg
    (A0 := ∫ ω, (T8.Ry mk X ξ c d [] ω - ∫ ω', T8.Ry mk X ξ c d [] ω' ∂P) ^ 2 ∂P)
    (σ2 := ∫ ω, (T8.Ry mk X ξ c d [0] ω
      - (∫ ω, DirectedOpinion.NoMemory.Z X U ξ [0] 0 ω ∂P) / (c + d - rho1 P mk X)) ^ 2 ∂P)
    hcd h1 h2 ?_ ?_ hrc hr0v ?_ ?_
  · rw [hm0, hr0, hEW0]
  · rw [hm1, hμ]; exact T8.ry_mean_child hGW [0] (by simp)
  · rw [hv0, hn0, hV0, hV1]
  · rw [hv1, T8.ry_mean_child hGW [0] (by simp), ← hμ, hn1, hV1]
