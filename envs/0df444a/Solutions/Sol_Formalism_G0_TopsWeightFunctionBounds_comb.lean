-- Prove2me | solution 1 for Formalism.G0.TopsWeightFunctionBounds.comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:03.03794+00:00
-- url     : https://prove2.me/submissions/46637594-fe08-4d82-81e8-0eb92620739d

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_append
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_runS_bad
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_even_mod
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_PRun_zero
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_inv_iter
import Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_Ls_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds
namespace Formalism.G0.TopsWeightFunctionBounds
theorem _root_.solution {n : ℕ} (hn2 : 2 ≤ n) (hn : Even n) {L₂ r N₁ : ℕ} (hr : 1 ≤ r) (K₀ : ℕ)
    (hK : 1 + 3 * r * K₀ ≤ N₁) (T : Finset ℕ) (h : ¬ CondB n T L₂ r N₁) :
    ∃ i < n, i ∈ T ∧
      runS (3 * r) L₂ (init K₀ (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad := by
  unfold CondB at h
  push_neg at h
  obtain ⟨b, e, hb, he, hcount, hno⟩ := h
  have hex : ∃ d, d ≤ e ∧ (b + d) % n ∈ T := by
    have hpos : 0 < ((Finset.range (e + 1)).filter fun d => (b + d) % n ∈ T).card := by omega
    obtain ⟨d, hd⟩ := Finset.card_pos.1 hpos
    rw [Finset.mem_filter, Finset.mem_range] at hd
    exact ⟨d, by omega, hd.2⟩
  classical
  let d₀ := Nat.find hex
  have hd₀ : d₀ ≤ e ∧ (b + d₀) % n ∈ T := Nat.find_spec hex
  have hmin : ∀ d < d₀, (b + d) % n ∉ T := by
    intro d hd hdT
    exact Nat.find_min hex hd ⟨by omega, hdT⟩
  have hi : (b + d₀) % n < n := Nat.mod_lt _ (by omega)
  refine ⟨(b + d₀) % n, hi, hd₀.2, ?_⟩
  have hevi : decide (Even ((b + d₀) % n)) = decide (Even (b + d₀)) := by
    simp only [even_mod hn]
  by_cases hK0 : K₀ = 0
  · simp only [init, hK0, if_true]; exact runS_bad _
  rw [init, if_neg hK0, hevi]
  have hR : 1 ≤ 3 * r := by omega
  have hinit : Inv n T L₂ (3 * r) b K₀ d₀ (.run K₀ 0 0 true (decide (Even (b + d₀)))) := by
    refine ⟨by omega, le_rfl, by omega, Nat.zero_le _, rfl, by simpa using hd₀.2,
      fun x h1 h2 => by omega, ?_, fun _ => ⟨Fin.elim0, PRun_zero _ _ _ _ _ _ _⟩⟩
    have : (Finset.range (d₀ + 1)).filter (fun d => (b + d) % n ∈ T) = {d₀} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        by_contra hne
        exact hmin x (by omega) h2
      · rintro rfl; exact ⟨by omega, hd₀.2⟩
    unfold cnt
    rw [this, Finset.card_singleton]
    simp
  have hI := inv_iter hn hR (e - d₀) d₀ _ hinit
  rw [show d₀ + (e - d₀) = e by omega] at hI
  have hL : (Lst n ((b + d₀) % n)).map (fun p => decide (p ∈ T)) = Ls n T b d₀ (n - 1) := by
    unfold Lst Ls
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    rw [add_assoc, Nat.mod_add_mod, show b + d₀ + (x + 1) = b + (d₀ + 1 + x) by omega]
  rw [hL, show n - 1 = (e - d₀) + (n - 1 - (e - d₀)) by omega]
  obtain ⟨rest, hrest⟩ := Ls_add n T b d₀ (e - d₀) (n - 1 - (e - d₀))
  rw [hrest, runS_append]
  generalize runS (3 * r) L₂ (St.run K₀ 0 0 true (decide (Even (b + d₀)))) (Ls n T b d₀ (e - d₀)) = st at hI ⊢
  cases st with
  | bad => exact runS_bad _
  | good => exact absurd hI hno
  | run K j d al ev =>
    exfalso
    obtain ⟨hK1, hK2, hj, -, -, -, -, hc, -⟩ := hI
    have hce : N₁ ≤ cnt n T b e := hcount
    have hm : 3 * r * (K₀ - K) + 3 * r ≤ 3 * r * K₀ := by
      rw [← mul_add_one]; exact Nat.mul_le_mul_left _ (by omega)
    omega
end Formalism.G0.TopsWeightFunctionBounds
