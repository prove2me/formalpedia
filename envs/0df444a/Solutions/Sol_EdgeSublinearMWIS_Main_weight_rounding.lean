-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.weight_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:19:17.882318+00:00
-- url     : https://prove2.me/submissions/88472606-4239-4cb9-93d3-5052beae2899

import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedHelpers

 def beforeCount {n : ℕ} (t : Fin n → ℕ) (v : Fin n) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u => u < v), t u

 theorem beforeCount_add {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v = ∑ u ∈ Finset.univ.filter (fun u => u ≤ v), t u := by
  classical
  have hset : Finset.univ.filter (fun u : Fin n => u ≤ v) =
      insert v (Finset.univ.filter (fun u : Fin n => u < v)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    exact le_iff_lt_or_eq.trans or_comm
  rw [hset, Finset.sum_insert (by simp)]
  exact Nat.add_comm _ _

 theorem beforeCount_le_total {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    beforeCount t v + t v ≤ totalCopies t := by
  classical
  rw [beforeCount_add]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

 theorem cumulative_le_beforeCount {n : ℕ} (t : Fin n → ℕ) {u v : Fin n} (huv : u < v) :
    (∑ x ∈ Finset.univ.filter (fun x => x ≤ u), t x) ≤ beforeCount t v := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_le_of_lt hx huv

 theorem owner_of_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (lo : beforeCount t v ≤ j.val) (hi : j.val < beforeCount t v + t v) :
    copyOwner t j = some v := by
  classical
  unfold copyOwner
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl]
  apply (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mpr
  refine ⟨?_, ?_⟩
  · simpa only [id_eq, decide_eq_true_eq, ← beforeCount_add] using hi
  · intro u huv
    simp only [decide_eq_true_eq, not_lt]
    exact (cumulative_le_beforeCount t huv).trans lo

 theorem owner_interval {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t))
    (v : Fin n) (h : copyOwner t j = some v) :
    beforeCount t v ≤ j.val ∧ j.val < beforeCount t v + t v := by
  classical
  unfold copyOwner at h
  rw [show List.finRange n = List.ofFn (fun v : Fin n => v) from rfl] at h
  have hh := (List.find?_ofFn_eq_some_of_injective (Function.injective_id)).mp h
  simp only [id_eq] at hh
  have hi : j.val < beforeCount t v + t v := by
    simpa only [decide_eq_true_eq, ← beforeCount_add] using hh.1
  refine ⟨?_, hi⟩
  by_cases hz : v.val = 0
  · have hv : ∀ u : Fin n, ¬ u < v := by intro u; simp only [Fin.lt_def]; omega
    simp [beforeCount, hv]
  · let u : Fin n := ⟨v.val - 1, by omega⟩
    have huv : u < v := by simp only [Fin.lt_def]; dsimp [u]; omega
    have hu := hh.2 u huv
    simp only [decide_eq_true_eq, not_lt] at hu
    have hset : Finset.univ.filter (fun x : Fin n => x ≤ u) =
        Finset.univ.filter (fun x : Fin n => x < v) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val,
        Fin.lt_def]
      dsimp [u]
      omega
    simpa [hset, beforeCount] using hu

 def copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    Fin (totalCopies t) :=
  ⟨beforeCount t v + i.val, (Nat.add_lt_add_left i.isLt _).trans_le (beforeCount_le_total t v)⟩

 theorem owner_copyIndex {n : ℕ} (t : Fin n → ℕ) (v : Fin n) (i : Fin (t v)) :
    copyOwner t (copyIndex t v i) = some v := by
  apply owner_of_interval
  · exact Nat.le_add_right _ _
  · exact Nat.add_lt_add_left i.isLt _

 theorem owner_exists {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    ∃ v, copyOwner t j = some v := by
  classical
  by_contra h
  have hnone : copyOwner t j = none := by
    cases he : copyOwner t j with
    | none => rfl
    | some v => exact False.elim (h ⟨v, he⟩)
  unfold copyOwner at hnone
  have hf := List.find?_eq_none.mp hnone
  by_cases hn : n = 0
  · subst n
    have hz : totalCopies t = 0 := by simp [totalCopies]
    have := j.isLt
    omega
  · let v : Fin n := ⟨n-1, by omega⟩
    have hp := hf v (by simp)
    simp only [decide_eq_true_eq, not_lt] at hp
    have heq : Finset.univ.filter (fun u : Fin n => u ≤ v) = Finset.univ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val]
      dsimp [v]
      have hu := u.isLt
      exact iff_true_intro (Nat.le_pred_of_lt u.isLt)
    rw [heq] at hp
    exact Nat.not_le_of_lt j.isLt hp

noncomputable def fiberEquiv {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    {j : Fin (totalCopies t) // copyOwner t j = some v} ≃ Fin (t v) where
  toFun j := ⟨j.val.val - beforeCount t v, by
    have h := owner_interval t j.val v j.property
    omega⟩
  invFun i := ⟨copyIndex t v i, owner_copyIndex t v i⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [copyIndex]
    have h := (owner_interval t j.val v j.property).1
    omega
  right_inv i := by
    apply Fin.ext
    simp [copyIndex]

 theorem fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => copyOwner t j = some v)).card = t v := by
  classical
  simpa only [Fintype.card_coe, Fintype.card_fin, Finset.card_univ, Fintype.card_subtype]
    using Fintype.card_congr (fiberEquiv t v)

 theorem max_weight_le {n : ℕ} (w : Fin n → ℚ) (v : Fin n) :
    w v ≤ maximumWeight w := by
  have hne : List.ofFn w ≠ [] := List.ne_nil_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)
  unfold maximumWeight
  rw [List.foldl_max_eq_max hne]
  exact (List.le_max_of_mem (List.mem_ofFn.mpr ⟨v, rfl⟩)).trans (le_max_right _ _)

 theorem max_weight_attained {n : ℕ} (w : Fin n → ℚ) (hpos : 0 < maximumWeight w) :
    ∃ v, maximumWeight w = w v := by
  have hne : List.ofFn w ≠ [] := by
    intro h
    have : maximumWeight w = 0 := by simp [maximumWeight, h]
    linarith
  have hEq : maximumWeight w = (List.ofFn w).max hne := by
    unfold maximumWeight at *
    rw [List.foldl_max_eq_max hne] at *
    exact max_eq_right (by by_contra h; rw [max_eq_left (le_of_not_ge h)] at hpos; linarith)
  have hmem := List.max_mem hne
  obtain ⟨v, hv⟩ := List.mem_ofFn.mp hmem
  exact ⟨v, hEq.trans hv.symm⟩

 theorem weightedAlpha_bdd {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : BddAbove {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      z = ∑ v ∈ I, (w v : ℝ)} := by
  classical
  apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).bddAbove.mono
  rintro z ⟨I, hI, hi, rfl⟩
  exact Set.mem_range_self _

 theorem weightedAlpha_member {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) (I : Finset (Fin n)) (hI : I ⊆ W) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (∑ v ∈ I, (w v : ℝ)) ≤ weightedAlphaOn G W w := by
  exact le_csSup (weightedAlpha_bdd G W w) ⟨I, hI, hind, rfl⟩

 theorem weightedAlpha_attained {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n))
    (w : Fin n → ℚ) : ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧
      weightedAlphaOn G W w = ∑ v ∈ I, (w v : ℝ) := by
  classical
  let S := {z : ℝ | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧ z = ∑ v ∈ I, (w v : ℝ)}
  have hne : S.Nonempty := by
    refine ⟨0, ∅, Finset.empty_subset _, ?_, by simp⟩
    simp
  have hfin : S.Finite := by
    apply (Set.finite_range (fun I : Finset (Fin n) => ∑ v ∈ I, (w v : ℝ))).subset
    rintro z ⟨I, hI, hi, rfl⟩
    exact Set.mem_range_self _
  exact hne.csSup_mem hfin

noncomputable def owner {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) : Fin n :=
  Classical.choose (owner_exists t j)

 theorem owner_spec {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) :
    copyOwner t j = some (owner t j) := Classical.choose_spec (owner_exists t j)

 theorem owner_eq_iff {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) (v : Fin n) :
    owner t j = v ↔ copyOwner t j = some v := by
  rw [owner_spec, Option.some.injEq]

 theorem owner_fiber_card {n : ℕ} (t : Fin n → ℕ) (v : Fin n) :
    (Finset.univ.filter (fun j => owner t j = v)).card = t v := by
  classical
  simp only [owner_eq_iff]
  exact fiber_card t v

 theorem rounded_adj_iff {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (i j : Fin (totalCopies t)) :
    (roundedGraph G t).Adj i j ↔ G.Adj (owner t i) (owner t j) := by
  constructor
  · rintro ⟨u, v, hu, hv, hadj⟩
    rw [← (owner_eq_iff t i u).mpr hu, ← (owner_eq_iff t j v).mpr hv] at hadj
    exact hadj
  · intro h
    exact ⟨owner t i, owner t j, owner_spec t i, owner_spec t j, h⟩

 theorem lift_card {n : ℕ} (t : Fin n → ℕ) (I : Finset (Fin n)) :
    (Finset.univ.filter (fun j => owner t j ∈ I)).card = ∑ v ∈ I, t v := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.sum_congr rfl (fun v hv => owner_fiber_card t v)

 theorem lift_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    (roundedGraph G t).IsIndepSet (Finset.univ.filter (fun j => owner t j ∈ I) : Set (Fin (totalCopies t))) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro i hi j hj hij hadj
  have h := (rounded_adj_iff G t i j).mp hadj
  exact hind (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 (G.ne_of_adj h) h

 theorem alpha_lift_bound {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin n)) (hind : G.IsIndepSet (I : Set (Fin n))) :
    ∑ v ∈ I, t v ≤ alpha (roundedGraph G t) Finset.univ := by
  classical
  rw [← lift_card]
  unfold alpha
  apply Finset.le_sup
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, lift_independent G t I hind⟩

 theorem originalVertices_eq {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : originalVertices t I = I.image (owner t) := by
  classical
  ext v
  simp only [originalVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image, owner_eq_iff]

 theorem projection_independent {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t)))
    (hind : (roundedGraph G t).IsIndepSet (I : Set (Fin (totalCopies t)))) :
    G.IsIndepSet (originalVertices t I : Set (Fin n)) := by
  rw [SimpleGraph.isIndepSet_iff] at hind ⊢
  intro u hu v hv huv hadj
  rw [originalVertices_eq] at hu hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have h := (rounded_adj_iff G t i j).mpr hadj
  exact hind hi hj ((roundedGraph G t).ne_of_adj h) h

 theorem projection_card_bound {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : I.card ≤ ∑ v ∈ originalVertices t I, t v := by
  classical
  rw [originalVertices_eq, Finset.card_eq_sum_card_image (owner t) I]
  apply Finset.sum_le_sum
  intro v hv
  rw [← owner_fiber_card t v]
  exact Finset.card_le_card (by intro j hj; simp_all only [Finset.mem_filter, Finset.mem_univ, true_and])

 theorem maximumWeight_le_alpha {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ)
    (hpos : 0 < maximumWeight w) : (maximumWeight w : ℝ) ≤ weightedAlpha G w := by
  classical
  obtain ⟨v, hv⟩ := max_weight_attained w hpos
  rw [hv]
  have h := weightedAlpha_member G Finset.univ w {v} (Finset.subset_univ _) (by simp)
  simpa [weightedAlpha] using h

end EdgeSublinearMWIS.Main.WeightedHelpers


open scoped BigOperators
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
set_option autoImplicit false

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) (ε : ℚ)
    (hn : 2 ≤ n) (hw : ∀ v, 0 ≤ w v) (hmax : 0 < maximumWeight w)
    (he : 0 < ε) (he1 : ε < 1) :
    ∃ (τ : ℚ) (t : Fin n → ℕ), weightRounding w ε = some (τ, t) ∧
      0 < τ ∧ τ = ε * maximumWeight w / (2 * (n : ℚ)) ∧
      (∀ v, t v = ⌊w v / τ⌋₊) ∧
      (totalCopies t : ℚ) ≤ 2 * (n : ℚ) ^ 2 / ε ∧
      (1 - (ε : ℝ) / 2) * weightedAlpha G w ≤
        (τ : ℝ) * alpha (roundedGraph G t) Finset.univ ∧
      ∀ I : Finset (Fin (totalCopies t)),
        (roundedGraph G t).IsIndepSet (I : Set (Fin (totalCopies t))) →
        G.IsIndepSet (originalVertices t I : Set (Fin n)) ∧
        (τ : ℝ) * I.card ≤ ∑ v ∈ originalVertices t I, (w v : ℝ) := by
  classical
  let τ : ℚ := ε * maximumWeight w / (2 * (n : ℚ))
  let t : Fin n → ℕ := fun v => ⌊w v / τ⌋₊
  have hnq : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  have hτ : 0 < τ := div_pos (mul_pos he hmax) (mul_pos (by norm_num) hnq)
  have hτR : (0 : ℝ) < τ := by exact_mod_cast hτ
  have floor_upper (v : Fin n) : τ * t v ≤ w v := by
    have hf := (Nat.floor_le (div_nonneg (hw v) hτ.le) : (t v : ℚ) ≤ w v / τ)
    simpa only [mul_comm] using (le_div_iff₀ hτ).mp hf
  have floor_lower (v : Fin n) : w v - τ ≤ τ * t v := by
    have h := (div_lt_iff₀ hτ).mp (Nat.lt_floor_add_one (w v / τ))
    change w v < ((t v : ℚ) + 1) * τ at h
    linarith
  have htotal : (totalCopies t : ℚ) ≤ 2 * (n : ℚ) ^ 2 / ε := by
    have hsum : τ * (totalCopies t : ℚ) ≤ (n : ℚ) * maximumWeight w := by
      calc
        τ * (totalCopies t : ℚ) = ∑ v, τ * (t v : ℚ) := by simp [totalCopies, Finset.mul_sum]
        _ ≤ ∑ v, w v := Finset.sum_le_sum (fun v hv => floor_upper v)
        _ ≤ ∑ _v : Fin n, maximumWeight w := Finset.sum_le_sum (fun v hv => max_weight_le w v)
        _ = (n : ℚ) * maximumWeight w := by simp
    have heq : (n : ℚ) * maximumWeight w / τ = 2 * (n : ℚ) ^ 2 / ε := by
      dsimp [τ]
      field_simp
    rw [← heq]
    exact (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hsum)
  refine ⟨τ, t, ?_, hτ, rfl, (fun v => rfl), htotal, ?_, ?_⟩
  · simp [weightRounding, show ¬n ≤ 1 by omega, not_le.mpr hmax,
      not_le.mpr he, not_le.mpr he1, hw, τ, t]
  · obtain ⟨I, hI, hind, hopt⟩ := weightedAlpha_attained G Finset.univ w
    have hlift : (∑ v ∈ I, (t v : ℝ)) ≤ alpha (roundedGraph G t) Finset.univ := by
      exact_mod_cast alpha_lift_bound G t I hind
    have hsum : (∑ v ∈ I, (w v : ℝ)) - I.card * (τ : ℝ) ≤
        (τ : ℝ) * ∑ v ∈ I, (t v : ℝ) := by
      rw [Finset.mul_sum, show (I.card : ℝ) * τ = ∑ _v ∈ I, (τ : ℝ) by simp, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro v hv
      exact_mod_cast floor_lower v
    have hnI : (I.card : ℝ) ≤ n := by exact_mod_cast (show I.card ≤ n by simpa using Finset.card_le_univ I)
    have hscale : (n : ℝ) * τ = (ε : ℝ) * maximumWeight w / 2 := by
      dsimp [τ]
      push_cast
      field_simp
    have hwmax := maximumWeight_le_alpha G w hmax
    have heR : (0 : ℝ) < ε := by exact_mod_cast he
    have hα : weightedAlpha G w = ∑ v ∈ I, (w v : ℝ) := by simpa [weightedAlpha] using hopt
    have hnt : (I.card : ℝ) * τ ≤ (n : ℝ) * τ := mul_le_mul_of_nonneg_right hnI hτR.le
    have hlast : (ε : ℝ) * maximumWeight w / 2 ≤ (ε : ℝ) * weightedAlpha G w / 2 := by gcongr
    have hmul := mul_le_mul_of_nonneg_left hlift hτR.le
    nlinarith
  · intro I hind
    refine ⟨projection_independent G t I hind, ?_⟩
    have hcard : (I.card : ℝ) ≤ ∑ v ∈ originalVertices t I, (t v : ℝ) := by
      exact_mod_cast projection_card_bound t I
    calc
      (τ : ℝ) * I.card ≤ (τ : ℝ) * ∑ v ∈ originalVertices t I, (t v : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hτR.le
      _ = ∑ v ∈ originalVertices t I, (τ : ℝ) * t v := by rw [Finset.mul_sum]
      _ ≤ ∑ v ∈ originalVertices t I, (w v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast floor_upper v
