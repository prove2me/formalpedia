-- Prove2me | solution 1 for AutoregLTF.eq_46
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:27:59.297545+00:00
-- url     : https://prove2.me/submissions/386589a7-51f5-492f-8cb4-dd66231113d8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_PACSampleComplexity
import Definitions.Def_AutoregLTF_ltf

section
set_option autoImplicit false
namespace AutoregLTF.Dev.Eq46
open AutoregLTF

lemma traj_zero (d : ℕ) (x : Fin d → Bool) (n : ℕ) (hn : d ≤ n) :
    traj (fun _ : Fin d => (0 : ℚ)) x n = false := by
  rw [traj]
  have : ¬ n < d := by omega
  simp [this]

lemma traj_one (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    traj (fun ℓ : Fin d => if ℓ.val = 0 then (1 : ℚ) else 0) (fun _ => true) n = true := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [traj]
    by_cases h : n < d
    · simp [h]
    · simp only [h, dif_neg, not_false_eq_true]
      have h0 : (⟨0, hd⟩ : Fin d) ∈ Finset.univ := Finset.mem_univ _
      rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
      · have := ih (n - 1) (by omega)
        simp [this]
      · intro b _ hb
        have : b.val ≠ 0 := fun h' => hb (Fin.ext h')
        simp [this]
      · intro h'; exact absurd h0 h'

end AutoregLTF.Dev.Eq46
namespace AutoregLTF
open AutoregLTF.Dev.Eq46 in
theorem chk_eq_46 (d T : ℕ) (hd : 1 ≤ d) (hT : 1 ≤ T) :
    ltf d T (fun _ => 0) (fun _ => true) = false ∧
    ltf d T (fun ℓ => if ℓ.val = 0 then 1 else 0) (fun _ => true) = true ∧
    1 ≤ QAlgorithms.Learning.vcDimSet (cls d T) := by
  have h0 : ltf d T (fun _ => 0) (fun _ => true) = false :=
    traj_zero d _ _ (by omega)
  have h1 : ltf d T (fun ℓ => if ℓ.val = 0 then 1 else 0) (fun _ => true) = true :=
    traj_one d hd _
  refine ⟨h0, h1, ?_⟩
  have hs : QAlgorithms.Learning.ShattersSet (cls d T) {fun _ : Fin d => true} := by
    intro y
    have hy : ∀ a : ({fun _ : Fin d => true} : Finset (Fin d → Bool)),
        a.1 = fun _ => true := fun a => Finset.mem_singleton.mp a.2
    cases hb : y ⟨fun _ => true, by simp⟩
    · refine ⟨ltf d T (fun _ => 0), ⟨_, rfl⟩, fun a => ?_⟩
      have : a = ⟨fun _ => true, by simp⟩ := Subtype.ext (hy a)
      subst this; simp [h0, hb]
    · refine ⟨ltf d T (fun ℓ => if ℓ.val = 0 then 1 else 0), ⟨_, rfl⟩, fun a => ?_⟩
      have : a = ⟨fun _ => true, by simp⟩ := Subtype.ext (hy a)
      subst this; simp [h1, hb]
  calc (1 : ℕ∞) = (({fun _ : Fin d => true} : Finset (Fin d → Bool)).card : ℕ∞) := by simp
    _ ≤ _ := le_iSup₂ (f := fun (s : Finset (Fin d → Bool))
        (_ : QAlgorithms.Learning.ShattersSet (cls d T) s) => (s.card : ℕ∞)) _ hs
end AutoregLTF
end

theorem solution : type_of% @AutoregLTF.chk_eq_46 := @AutoregLTF.chk_eq_46
