-- Prove2me | solution 1 for Formalism.FN.partialBoxVolumeMonotoneStep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:40.741557+00:00
-- url     : https://prove2.me/submissions/4e604863-8029-446d-8fc4-8cac762a326d

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_GjLevel
import Theorems.Thm_Formalism_FN_measurableSet_boxJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
namespace Formalism.FN
theorem _root_.solution : GjLevel := by
  intro n j A hj hA hinj
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin n, (jj : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
  let ej : Fin n → ℝ := Pi.single jj 1
  have ej_apply : ∀ i, ej i = if i = jj then 1 else 0 := fun i => by simp [ej, Pi.single_apply]
  have hcoord : ∀ (y : Fin n → ℝ) (m : ℤ) (i : Fin n),
      (y + (m : ℝ) • ej) i = if i = jj then y i + m else y i := by
    intro y m i
    simp only [Pi.add_apply, Pi.smul_apply, ej_apply, smul_eq_mul]
    split_ifs <;> ring

  let S : Set (Fin n → ℝ) := boxJ n j ∩ (A + latJ n j)
  let P : ℤ → Set (Fin n → ℝ) := fun m => S ∩ {x | ⌊x jj⌋ = m}
  let Q : ℤ → Set (Fin n → ℝ) := fun m => (fun y => y + (m : ℝ) • ej) ⁻¹' P m
  have hSm : MeasurableSet S := (measurableSet_boxJ n j).inter (hA.add_right (t := latJ n j)).measurableSet
  have hPm : ∀ m, MeasurableSet (P m) := fun m =>
    hSm.inter ((Int.measurable_floor.comp (measurable_pi_apply jj)) (measurableSet_singleton m))
  have hQm : ∀ m, MeasurableSet (Q m) := fun m => (measurable_id.add_const _) (hPm m)
  have hvol : ∀ m, volume (Q m) = volume (P m) := fun m =>
    measure_preimage_add_right volume _ (P m)
  have hsub : ∀ m, Q m ⊆ boxJ n (j + 1) ∩ (A + latJ n (j + 1)) := by
    intro m y hy
    obtain ⟨⟨hbox, hAk⟩, hfl⟩ := hy
    have hfl' : ⌊(y + (m : ℝ) • ej) jj⌋ = m := hfl
    rw [hcoord, if_pos rfl, Int.floor_add_intCast] at hfl'
    have h0 : ⌊y jj⌋ = 0 := by omega
    have hyj := Int.floor_eq_zero_iff.1 h0
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hij : i = jj
      · subst hij; exact ⟨hyj.1, hyj.2⟩
      · have hlt : (i : ℕ) < j :=
          lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => hij (Fin.ext (h.trans hjj.symm)))
        have hb : 0 ≤ (y + (m : ℝ) • ej) i ∧ (y + (m : ℝ) • ej) i < 1 := hbox i hlt
        rw [hcoord, if_neg hij] at hb
        exact hb
    · obtain ⟨a, ha, k, hk, hak0⟩ := hAk
      have hak : a + k = y + (m : ℝ) • ej := hak0
      refine Set.mem_add.2 ⟨a, ha, k - (m : ℝ) • ej, ⟨?_, ?_⟩, ?_⟩
      · intro i
        obtain ⟨z, hz⟩ := hk.1 i
        refine ⟨z - (if i = jj then m else 0), ?_⟩
        simp only [Pi.sub_apply, Pi.smul_apply, ej_apply, smul_eq_mul, hz]
        split_ifs <;> push_cast <;> ring
      · intro i hi
        have hne : i ≠ jj := fun h => by rw [h, hjj] at hi; omega
        simp [hk.2 i (by omega), ej_apply, hne]
      · rw [← add_sub_assoc, hak, add_sub_cancel_right]
  have hdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro m m' hmm'
    rw [Function.onFun, Set.disjoint_left]
    intro y hy hy'
    obtain ⟨⟨_, hAk⟩, _⟩ := hy
    obtain ⟨⟨_, hAk'⟩, _⟩ := hy'
    obtain ⟨a, ha, k, hk, hak0⟩ := hAk
    obtain ⟨a', ha', k', hk', hak0'⟩ := hAk'
    have hak : a + k = y + (m : ℝ) • ej := hak0
    have hak' : a' + k' = y + (m' : ℝ) • ej := hak0'
    have hint : ∀ i, ∃ z : ℤ, a i - a' i = z := by
      intro i
      obtain ⟨z, hz⟩ := hk.1 i
      obtain ⟨z', hz'⟩ := hk'.1 i
      have e1 := congrFun hak i
      have e2 := congrFun hak' i
      rw [Pi.add_apply, hcoord] at e1 e2
      split_ifs at e1 e2
      · exact ⟨m - m' - z + z', by push_cast; linarith⟩
      · exact ⟨-z + z', by push_cast; linarith⟩
    have hjeq := hinj a ha a' ha' hint jj hjj.ge
    have hk0 : k jj = 0 := hk.2 jj hjj.ge
    have hk0' : k' jj = 0 := hk'.2 jj hjj.ge
    have e1 := congrFun hak jj
    have e2 := congrFun hak' jj
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0, add_zero] at e1
    rw [Pi.add_apply, hcoord, if_pos rfl, hk0', add_zero] at e2
    apply hmm'
    exact_mod_cast (by linarith : (m : ℝ) = m')
  have hcover : S ⊆ ⋃ m : ℤ, P m := fun x hx => Set.mem_iUnion.2 ⟨⌊x jj⌋, hx, rfl⟩
  calc Gj n j A = volume S := rfl
    _ ≤ volume (⋃ m : ℤ, P m) := measure_mono hcover
    _ ≤ ∑' m, volume (P m) := measure_iUnion_le _
    _ = ∑' m, volume (Q m) := tsum_congr fun m => (hvol m).symm
    _ = volume (⋃ m, Q m) := (measure_iUnion hdisj hQm).symm
    _ ≤ volume (boxJ n (j + 1) ∩ (A + latJ n (j + 1))) := measure_mono (Set.iUnion_subset hsub)
    _ = Gj n (j + 1) A := rfl
end Formalism.FN
