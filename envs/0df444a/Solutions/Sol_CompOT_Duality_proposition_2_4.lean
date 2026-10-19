-- Prove2me | solution 1 for CompOT.Duality.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T00:55:22.839581+00:00
-- url     : https://prove2.me/submissions/93742d0d-cb14-4103-b07b-144e90643b83

-- Licensed under Apache 2.0. Full exact theorem: finite Kantorovich duality with both attainments.
import Mathlib
import Definitions.Def_CompOT_Duality_Defs


open scoped BigOperators
open CompOT.Assignment

namespace OTMetricProof

lemma coupling_entry_le_row {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ a i := by
  rw [← hP.2.1 i]
  exact Finset.single_le_sum (fun k _ => hP.1 i k) (Finset.mem_univ j)

lemma coupling_entry_le_col {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ b j := by
  rw [← hP.2.2 j]
  exact Finset.single_le_sum (fun k _ => hP.1 k j) (Finset.mem_univ i)

lemma product_coupling {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (fun i j => a i * b j) ∈ couplings a b := by
  refine ⟨fun i j => mul_nonneg (ha.1 i) (hb.1 j), ?_, ?_⟩
  · intro i
    simp only [← Finset.mul_sum, hb.2, mul_one]
  · intro j
    simp only [← Finset.sum_mul, ha.2, one_mul]

lemma coupling_nonempty {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (couplings a b).Nonempty := ⟨_, product_coupling ha hb⟩

lemma coupling_transpose {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) :
    P.transpose ∈ couplings b a :=
  ⟨fun i j => hP.1 j i, hP.2.2, hP.2.1⟩

lemma coupling_isClosed {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    IsClosed (couplings a b) := by
  change IsClosed {P : Matrix (Fin n) (Fin m) ℝ | (∀ i j, 0 ≤ P i j) ∧
    (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j)}
  have h₁ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, 0 ≤ P i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (continuous_const (y := (0 : ℝ)))
        (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => P i j) by fun_prop)
  have h₂ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i, ∑ j, P i j = a i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ j, P i j) by fun_prop)
      continuous_const
  have h₃ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ j, ∑ i, P i j = b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ i, P i j) by fun_prop)
      continuous_const
  exact h₁.inter (h₂.inter h₃)

lemma coupling_isCompact {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (_hb : b ∈ stdSimplex ℝ (Fin m)) :
    IsCompact (couplings a b) := by
  have hbox : IsCompact (Set.Icc (0 : Fin n → Fin m → ℝ)
      (fun _ _ => (1 : ℝ))) := isCompact_Icc
  refine hbox.of_isClosed_subset (coupling_isClosed a b) ?_
  intro P hP
  show P ∈ Set.Icc (0 : Fin n → Fin m → ℝ) (fun _ _ => 1)
  exact ⟨hP.1, fun i j => (coupling_entry_le_row hP i j).trans
    (mem_Icc_of_mem_stdSimplex ha i).2⟩

end OTMetricProof


open scoped BigOperators
open CompOT.Assignment

namespace OTMetricProof

lemma continuous_frob {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (frob C) := by
  unfold frob
  fun_prop

lemma exists_optimal {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃ P, IsOptimalCoupling C a b P := by
  obtain ⟨P, hP, hmin⟩ := (coupling_isCompact ha hb).exists_isMinOn
    (coupling_nonempty ha hb) (continuous_frob C).continuousOn
  exact ⟨P, hP, fun Q hQ => hmin hQ⟩

end OTMetricProof


open scoped BigOperators
open CompOT.Assignment CompOT.Duality

namespace OTDualityProof

lemma weak_duality {n m : ℕ} {C P : Matrix (Fin n) (Fin m) ℝ}
    {a f : Fin n → ℝ} {b g : Fin m → ℝ}
    (hP : P ∈ couplings a b) (hfg : dualFeasible C f g) :
    dualObj a b f g ≤ frob C P := by
  have he : dualObj a b f g = ∑ i, ∑ j, (f i + g j) * P i j := by
    simp only [dualObj, add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => g j * P i j)]
    simp only [← Finset.mul_sum, hP.2.1, hP.2.2]
  rw [he]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (hfg i j) (hP.1 i j)

end OTDualityProof


open scoped BigOperators Topology
open Filter CompOT.Assignment

namespace OTDualityProof

abbrev MarginalCost (n m : ℕ) := ((Fin n → ℝ) × (Fin m → ℝ)) × ℝ

def transportEpigraph {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    Set (MarginalCost n m) :=
  {x | ∃ P ∈ couplings x.1.1 x.1.2, frob C P ≤ x.2}

lemma epigraph_isClosed {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    IsClosed (transportEpigraph C) := by
  apply IsSeqClosed.isClosed
  intro x y hx hxy
  choose P hP hcost using hx
  have hbound (i : Fin n) : ∃ B : ℝ, ∀ k, (x k).1.1 i ≤ B := by
    have ht : Tendsto (fun k => (x k).1.1 i) atTop (𝓝 (y.1.1 i)) :=
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).continuousAt.tendsto.comp hxy
    obtain ⟨B, hB⟩ := ht.bddAbove_range
    exact ⟨B, fun k => hB (Set.mem_range_self k)⟩
  choose B hB using hbound
  have hbox : IsCompact (Set.Icc (0 : Fin n → Fin m → ℝ) (fun i _ => B i)) :=
    isCompact_Icc
  have hmem (k : ℕ) : P k ∈ Set.Icc (0 : Fin n → Fin m → ℝ) (fun i _ => B i) :=
    ⟨(hP k).1, fun i j => (OTMetricProof.coupling_entry_le_row (hP k) i j).trans (hB i k)⟩
  obtain ⟨Q, hQ, φ, hφ, hlim⟩ := hbox.tendsto_subseq hmem
  have hxlim := hxy.comp hφ.tendsto_atTop
  refine ⟨Q, ⟨hQ.1, ?_, ?_⟩, ?_⟩
  · intro i
    have hl : Tendsto (fun k => ∑ j, P (φ k) i j) atTop (𝓝 (∑ j, Q i j)) :=
      (show Continuous (fun R : Matrix (Fin n) (Fin m) ℝ => ∑ j, R i j) by
        fun_prop).continuousAt.tendsto.comp hlim
    have hr : Tendsto (fun k => (x (φ k)).1.1 i) atTop (𝓝 (y.1.1 i)) :=
      ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).continuousAt.tendsto.comp hxlim
    exact tendsto_nhds_unique hl (by simpa only [(hP _).2.1] using hr)
  · intro j
    have hl : Tendsto (fun k => ∑ i, P (φ k) i j) atTop (𝓝 (∑ i, Q i j)) :=
      (show Continuous (fun R : Matrix (Fin n) (Fin m) ℝ => ∑ i, R i j) by
        fun_prop).continuousAt.tendsto.comp hlim
    have hr : Tendsto (fun k => (x (φ k)).1.2 j) atTop (𝓝 (y.1.2 j)) :=
      ((continuous_apply j).comp (continuous_snd.comp continuous_fst)).continuousAt.tendsto.comp hxlim
    exact tendsto_nhds_unique hl (by simpa only [(hP _).2.2] using hr)
  · exact le_of_tendsto_of_tendsto
      ((OTMetricProof.continuous_frob C).continuousAt.tendsto.comp hlim)
      (continuous_snd.continuousAt.tendsto.comp hxlim)
      (Filter.Eventually.of_forall fun k => hcost (φ k))

lemma epigraph_zero {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    0 ∈ transportEpigraph C := by
  refine ⟨0, ⟨?_, ?_, ?_⟩, ?_⟩ <;> simp [frob]

lemma epigraph_add {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {x y : MarginalCost n m} (hx : x ∈ transportEpigraph C)
    (hy : y ∈ transportEpigraph C) : x + y ∈ transportEpigraph C := by
  obtain ⟨P, hP, hp⟩ := hx
  obtain ⟨Q, hQ, hq⟩ := hy
  refine ⟨P + Q, ⟨fun i j => add_nonneg (hP.1 i j) (hQ.1 i j), ?_, ?_⟩, ?_⟩
  · intro i
    change (∑ j, (P + Q) i j) = x.1.1 i + y.1.1 i
    simpa only [Matrix.add_apply, Finset.sum_add_distrib] using congrArg₂ (· + ·) (hP.2.1 i) (hQ.2.1 i)
  · intro j
    change (∑ i, (P + Q) i j) = x.1.2 j + y.1.2 j
    simpa only [Matrix.add_apply, Finset.sum_add_distrib] using congrArg₂ (· + ·) (hP.2.2 j) (hQ.2.2 j)
  · change frob C (P + Q) ≤ x.2 + y.2
    simpa only [frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib] using add_le_add hp hq

lemma epigraph_smul {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {x : MarginalCost n m} (hx : x ∈ transportEpigraph C) {r : ℝ} (hr : 0 ≤ r) :
    r • x ∈ transportEpigraph C := by
  obtain ⟨P, hP, hp⟩ := hx
  refine ⟨r • P, ⟨fun i j => mul_nonneg hr (hP.1 i j), ?_, ?_⟩, ?_⟩
  · intro i
    change (∑ j, (r • P) i j) = r * x.1.1 i
    simpa only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum] using congrArg (r * ·) (hP.2.1 i)
  · intro j
    change (∑ i, (r • P) i j) = r * x.1.2 j
    simpa only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum] using congrArg (r * ·) (hP.2.2 j)
  · change frob C (r • P) ≤ r * x.2
    simpa only [frob, Matrix.smul_apply, smul_eq_mul, mul_left_comm (C _ _) r,
      ← Finset.mul_sum] using mul_le_mul_of_nonneg_left hp hr

def transportCone {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    ProperCone ℝ (MarginalCost n m) where
  carrier := transportEpigraph C
  zero_mem' := epigraph_zero C
  add_mem' := epigraph_add
  smul_mem' := fun r _ hx => epigraph_smul hx r.2
  isClosed' := epigraph_isClosed C

end OTDualityProof


open scoped BigOperators Topology
open CompOT.Assignment CompOT.Duality

namespace OTDualityProof

lemma functional_expansion {n m : ℕ} (l : MarginalCost n m →L[ℝ] ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (z : ℝ) :
    l ((a, b), z) =
      (∑ i, l ((Pi.single i 1, 0), 0) * a i) +
      (∑ j, l ((0, Pi.single j 1), 0) * b j) + l ((0, 0), 1) * z := by
  have ha : ((a, (0 : Fin m → ℝ)), (0 : ℝ)) =
      ∑ i, a i • (((Pi.single i 1 : Fin n → ℝ), 0), 0) := by
    ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, mul_ite]
  have hb : (((0 : Fin n → ℝ), b), (0 : ℝ)) =
      ∑ j, b j • ((0, (Pi.single j 1 : Fin m → ℝ)), 0) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply, mul_ite]
  have hz : (((0 : Fin n → ℝ), (0 : Fin m → ℝ)), z) =
      z • (((0 : Fin n → ℝ), (0 : Fin m → ℝ)), (1 : ℝ)) := by simp
  have he : ((a, b), z) = ((a, 0), 0) + ((0, b), 0) + ((0, 0), z) := by simp
  rw [he, map_add, map_add, ha, hb, hz, map_sum, map_sum, map_smul]
  simp only [map_smul, smul_eq_mul, mul_comm]

lemma single_entry_epigraph {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (i : Fin n) (j : Fin m) :
    ((Pi.single i 1, Pi.single j 1), C i j) ∈ transportEpigraph C := by
  let P : Matrix (Fin n) (Fin m) ℝ := fun k l => if k = i then if l = j then 1 else 0 else 0
  refine ⟨P, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro k l
    dsimp [P]
    split_ifs <;> norm_num
  · intro k
    by_cases h : k = i <;> simp [P, h]
  · intro l
    by_cases h : l = j <;> simp [P, h]
  · simp [frob, P, mul_ite]

lemma approximate_dual {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ} {P : Matrix (Fin n) (Fin m) ℝ}
    (hP : IsOptimalCoupling C a b P) {v : ℝ} (hv : v < frob C P) :
    ∃ f g, dualFeasible C f g ∧ v < dualObj a b f g := by
  have hx : ((a, b), v) ∉ transportCone C := by
    rintro ⟨Q, hQ, hcost⟩
    exact (not_le_of_gt hv) ((hP.2 Q hQ).trans hcost)
  obtain ⟨l, hnonneg, hneg⟩ := (transportCone C).hyperplane_separation_point hx
  let α : Fin n → ℝ := fun i => l ((Pi.single i 1, 0), 0)
  let β : Fin m → ℝ := fun j => l ((0, Pi.single j 1), 0)
  let γ : ℝ := l ((0, 0), 1)
  have hprimal : 0 ≤ l ((a, b), frob C P) := hnonneg _ ⟨P, hP.1, le_rfl⟩
  have hγ : 0 < γ := by
    rw [functional_expansion] at hprimal hneg
    change 0 ≤ (∑ i, α i * a i) + (∑ j, β j * b j) + γ * frob C P at hprimal
    change (∑ i, α i * a i) + (∑ j, β j * b j) + γ * v < 0 at hneg
    by_contra hn
    have hg := le_of_not_gt hn
    have := mul_le_mul_of_nonpos_left hv.le hg
    linarith
  have hc (i : Fin n) (j : Fin m) : 0 ≤ α i + β j + γ * C i j := by
    have hh := hnonneg _ (single_entry_epigraph C i j)
    rw [functional_expansion] at hh
    simpa [α, β, γ, Pi.single_apply, mul_ite] using hh
  refine ⟨fun i => -α i / γ, fun j => -β j / γ, ?_, ?_⟩
  · intro i j
    rw [← add_div, div_le_iff₀ hγ]
    have := hc i j
    nlinarith
  · have he : dualObj a b (fun i => -α i / γ) (fun j => -β j / γ) =
        -((∑ i, α i * a i) + (∑ j, β j * b j)) / γ := by
      simp only [dualObj, div_mul_eq_mul_div, neg_mul, ← Finset.sum_div,
        Finset.sum_neg_distrib, ← add_div]
      ring
    rw [he, lt_div_iff₀ hγ]
    rw [functional_expansion] at hneg
    change (∑ i, α i * a i) + (∑ j, β j * b j) + γ * v < 0 at hneg
    nlinarith

end OTDualityProof


noncomputable section
open Finset
open CompOT.Duality
namespace OTDualityProof

variable {n m : ℕ}

theorem simplex_index_nonempty {a : Fin n → ℝ} (ha : a ∈ stdSimplex ℝ (Fin n)) :
    Nonempty (Fin n) := by
  by_contra h
  have : IsEmpty (Fin n) := not_nonempty_iff.mp h
  simpa using ha.2

theorem cTransform_le (C : Matrix (Fin n) (Fin m) ℝ)
    (f : Fin n → ℝ) (i : Fin n) (j : Fin m) : cTransform C f j ≤ C i j - f i :=
  ciInf_le (Set.finite_range (fun k => C k j - f k)).bddBelow i

theorem cbarTransform_le (C : Matrix (Fin n) (Fin m) ℝ)
    (g : Fin m → ℝ) (i : Fin n) (j : Fin m) : cbarTransform C g i ≤ C i j - g j :=
  ciInf_le (Set.finite_range (fun k => C i k - g k)).bddBelow j

theorem cbarTransform_attained [Nonempty (Fin m)] (C : Matrix (Fin n) (Fin m) ℝ)
    (g : Fin m → ℝ) (i : Fin n) : ∃ j, C i j - g j = cbarTransform C g i :=
  exists_eq_ciInf_of_finite

theorem cTransform_feasible (C : Matrix (Fin n) (Fin m) ℝ)
    (f : Fin n → ℝ) : dualFeasible C f (cTransform C f) := by
  intro i j
  have h := cTransform_le C f i j
  linarith

theorem cbarTransform_feasible (C : Matrix (Fin n) (Fin m) ℝ)
    (g : Fin m → ℝ) : dualFeasible C (cbarTransform C g) g := by
  intro i j
  have h := cbarTransform_le C g i j
  linarith

theorem le_cbarTransform [Nonempty (Fin m)] {C : Matrix (Fin n) (Fin m) ℝ}
    {f : Fin n → ℝ} {g : Fin m → ℝ} (h : dualFeasible C f g) (i : Fin n) :
    f i ≤ cbarTransform C g i := by
  apply le_ciInf
  intro j
  have hij := h i j
  linarith

theorem le_cTransform [Nonempty (Fin n)] {C : Matrix (Fin n) (Fin m) ℝ}
    {f : Fin n → ℝ} {g : Fin m → ℝ} (h : dualFeasible C f g) (j : Fin m) :
    g j ≤ cTransform C f j := by
  apply le_ciInf
  intro i
  have hij := h i j
  linarith

end OTDualityProof


noncomputable section
open Finset
open CompOT.Duality
namespace OTDualityProof

variable {n m : ℕ}

def costBound (C : Matrix (Fin n) (Fin m) ℝ) : ℝ := ∑ i, ∑ j, |C i j|

theorem costBound_nonneg (C : Matrix (Fin n) (Fin m) ℝ) : 0 ≤ costBound C :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_costBound (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    |C i j| ≤ costBound C := by
  exact (single_le_sum (fun k _ => abs_nonneg (C i k)) (mem_univ j)).trans
    (single_le_sum (fun k _ => sum_nonneg fun l _ => abs_nonneg (C k l)) (mem_univ i))

theorem cost_bounds (C : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    -costBound C ≤ C i j ∧ C i j ≤ costBound C :=
  abs_le.mp (abs_le_costBound C i j)

theorem cbar_oscillation [Nonempty (Fin m)] (C : Matrix (Fin n) (Fin m) ℝ)
    (g : Fin m → ℝ) (i l : Fin n) :
    cbarTransform C g i - cbarTransform C g l ≤ 2 * costBound C := by
  obtain ⟨j, hj⟩ := cbarTransform_attained C g l
  have hi := cbarTransform_le C g i j
  have hci := cost_bounds C i j
  have hcl := cost_bounds C l j
  linarith

theorem dualObj_mono {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    {f F : Fin n → ℝ} {g G : Fin m → ℝ} (hf : ∀ i, f i ≤ F i) (hg : ∀ j, g j ≤ G j) :
    dualObj a b f g ≤ dualObj a b F G := by
  exact add_le_add (sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hf i) (ha i))
    (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hg j) (hb j))

theorem dualObj_gauge {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : ∑ i, a i = 1) (hb : ∑ j, b j = 1)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (t : ℝ) :
    dualObj a b (fun i => f i - t) (fun j => g j + t) = dualObj a b f g := by
  unfold dualObj
  simp only [sub_mul, add_mul, sum_sub_distrib, sum_add_distrib, ← mul_sum, ha, hb, mul_one]
  ring

theorem bounded_dual_improvement {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) {f : Fin n → ℝ} {g : Fin m → ℝ}
    (hfg : dualFeasible C f g) :
    ∃ F G, dualFeasible C F G ∧ dualObj a b f g ≤ dualObj a b F G ∧
      (∀ i, -(2 * costBound C) ≤ F i ∧ F i ≤ 2 * costBound C) ∧
      (∀ j, -(3 * costBound C) ≤ G j ∧ G j ≤ 3 * costBound C) := by
  let := simplex_index_nonempty ha
  let := simplex_index_nonempty hb
  let i₀ : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let F := cbarTransform C g
  let G := cTransform C F
  let t := F i₀
  have hF : ∀ i, -(2 * costBound C) ≤ F i - t ∧ F i - t ≤ 2 * costBound C := by
    intro i
    have h₁ := cbar_oscillation C g i i₀
    have h₂ := cbar_oscillation C g i₀ i
    dsimp [F, t]
    constructor <;> linarith
  refine ⟨(fun i => F i - t), (fun j => G j + t), ?_, ?_, hF, ?_⟩
  · intro i j
    have h := cTransform_feasible C F i j
    dsimp [G]
    linarith
  · rw [dualObj_gauge ha.2 hb.2]
    exact dualObj_mono ha.1 hb.1 (le_cbarTransform hfg)
      (le_cTransform (cbarTransform_feasible C g))
  · intro j
    have hlow : -(3 * costBound C) - t ≤ G j := by
      apply le_ciInf
      intro i
      have hci := cost_bounds C i j
      have hfi := hF i
      linarith
    have hu := cTransform_le C F i₀ j
    have hci := cost_bounds C i₀ j
    have hM := costBound_nonneg C
    change G j ≤ C i₀ j - t at hu
    constructor <;> linarith

end OTDualityProof


noncomputable section
open Finset
open CompOT.Duality
namespace OTDualityProof

variable {n m : ℕ}

def boundedDuals (C : Matrix (Fin n) (Fin m) ℝ) :
    Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {u | dualFeasible C u.1 u.2 ∧
    (∀ i, -(2 * costBound C) ≤ u.1 i ∧ u.1 i ≤ 2 * costBound C) ∧
    (∀ j, -(3 * costBound C) ≤ u.2 j ∧ u.2 j ≤ 3 * costBound C)}

theorem continuous_dualObj (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Continuous (fun u : (Fin n → ℝ) × (Fin m → ℝ) => dualObj a b u.1 u.2) := by
  unfold dualObj
  fun_prop

theorem boundedDuals_isCompact (C : Matrix (Fin n) (Fin m) ℝ) :
    IsCompact (boundedDuals C) := by
  have hfeas : IsClosed {u : (Fin n → ℝ) × (Fin m → ℝ) | dualFeasible C u.1 u.2} := by
    unfold dualFeasible
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (by fun_prop) continuous_const
  have heq : boundedDuals C =
      {u : (Fin n → ℝ) × (Fin m → ℝ) | dualFeasible C u.1 u.2} ∩
      Set.Icc ((fun _ => -(2 * costBound C)), (fun _ => -(3 * costBound C)))
        ((fun _ => 2 * costBound C), (fun _ => 3 * costBound C)) := by
    ext u
    simp only [boundedDuals, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      Prod.le_def, Pi.le_def]
    aesop
  rw [heq]
  exact isCompact_Icc.inter_left hfeas

theorem exists_dual_optimal (C : Matrix (Fin n) (Fin m) ℝ)
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃ f g, IsDualOptimal C a b f g := by
  have hbase : dualFeasible C (fun _ => -costBound C) (fun _ => 0) := by
    intro i j
    simpa using (cost_bounds C i j).1
  obtain ⟨f₀, g₀, hfg₀, _, hf₀, hg₀⟩ := bounded_dual_improvement ha hb C hbase
  have hne : (boundedDuals C).Nonempty := ⟨(f₀, g₀), hfg₀, hf₀, hg₀⟩
  obtain ⟨u, hu, hmax⟩ := (boundedDuals_isCompact C).exists_isMaxOn hne
    (continuous_dualObj a b).continuousOn
  refine ⟨u.1, u.2, hu.1, ?_⟩
  intro f g hfg
  obtain ⟨F, G, hFG, himp, hF, hG⟩ := bounded_dual_improvement ha hb C hfg
  exact himp.trans (hmax (show (F, G) ∈ boundedDuals C from ⟨hFG, hF, hG⟩))

end OTDualityProof


open CompOT.Assignment CompOT.Duality

namespace OTDualityProof

lemma native_duality {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ),
      IsOptimalCoupling C a b P ∧ IsDualOptimal C a b f g ∧
        frob C P = dualObj a b f g := by
  obtain ⟨P, hP⟩ := OTMetricProof.exists_optimal C ha hb
  obtain ⟨f, g, hfg⟩ := exists_dual_optimal C ha hb
  refine ⟨P, f, g, hP, hfg, le_antisymm ?_ (weak_duality hP.1 hfg.1)⟩
  by_contra hn
  have hlt : dualObj a b f g < frob C P := lt_of_not_ge hn
  obtain ⟨f', g', hfeas, hgt⟩ := approximate_dual C hP hlt
  exact (not_le_of_gt hgt) (hfg.2 f' g' hfeas)

end OTDualityProof


namespace CompOT.Duality

/-- Proposition 2.4, p. 382 (Kantorovich duality (2.20)): for histograms `a ∈ Σ_n`, `b ∈ Σ_m` and
any cost matrix `C`, the minimum `L_C(a, b)` of (2.11) is attained by some `P ∈ U(a, b)`, the maximum
of `⟨f, a⟩ + ⟨g, b⟩` over `R(C)` is attained by some `(f, g)`, and the two values are equal. -/
theorem proposition_2_4 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ),
      CompOT.Assignment.IsOptimalCoupling C a b P ∧ IsDualOptimal C a b f g ∧ CompOT.Assignment.frob C P = dualObj a b f g := by
  exact OTDualityProof.native_duality a b ha hb C

end CompOT.Duality

open CompOT.Duality

theorem solution {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ),
      CompOT.Assignment.IsOptimalCoupling C a b P ∧ IsDualOptimal C a b f g ∧ CompOT.Assignment.frob C P = dualObj a b f g := CompOT.Duality.proposition_2_4 a b ha hb C
