-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.gammaStableOfGammaQUnit_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:23.194041+00:00
-- url     : https://prove2.me/submissions/8774d62d-f6ac-4080-846f-0adde1fdf9ad

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_MemCoboundariesOfIsOneCoboundary
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_GammaStableOfGammaQUnitHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : GammaQNOf := by
  intro O A _ _ _ B M D _ _ _ _ N γ hG hQ hγ hN y hy
  obtain ⟨v, hvu, ⟨t, hvt⟩, hγQ⟩ := hG
  have hit : ∀ (k : ℕ) (x : D), (fun x : D => B.Q • x)^[k] x = B.Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hQM : Function.Bijective (fun x : D => B.Q ^ M • x) := by
    have h := hQ.iterate M
    rwa [show (fun x : D => B.Q • x)^[M] = fun x => B.Q ^ M • x from funext (hit M)] at h
  have hvk : ∀ k : ℕ, ∃ s : A, v ^ k = 1 + B.X * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      exact ⟨s + t + B.X * s * t, by rw [pow_succ, hs, hvt]; ring⟩
  obtain ⟨s, hs⟩ := hvk M
  have hγn : γ (B.Q ^ M • y) = v ^ M • B.Q ^ M • γ y := by
    rw [hγ, map_pow, hγQ, mul_pow, mul_smul]
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  obtain ⟨u, hu⟩ := hvu.pow M
  have hQγ : B.Q ^ M • γ y ∈ N := by
    have h1 : γ (B.Q ^ M • y) ∈ N := by
      have e : γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n' := by rw [← hn']; abel
      rw [e]
      exact N.add_mem hy (N.smul_mem _ hn'N)
    have h2 : B.Q ^ M • γ y = ((u⁻¹ : Aˣ) : A) • γ (B.Q ^ M • y) := by
      rw [hγn, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact N.smul_mem _ h1
  have hmN : n' - s • B.Q ^ M • γ y ∈ N := N.sub_mem hn'N (N.smul_mem _ hQγ)
  have hkey : B.Q ^ M • (γ y - y) = B.X • (n' - s • B.Q ^ M • γ y) := by
    have e : (1 + B.X * s) • B.Q ^ M • γ y - B.Q ^ M • y = B.X • n' := by
      rw [← hs, ← hγn]
      exact hn'
    rw [smul_sub, smul_sub, ← e, add_smul, one_smul, mul_smul]
    abel
  obtain ⟨y', hy'⟩ := hQM.2 (n' - s • B.Q ^ M • γ y)
  simp only at hy'
  refine ⟨y', by rw [hy']; exact hmN, ?_⟩
  apply hQM.1
  show B.Q ^ M • (γ y - y) = B.Q ^ M • (B.X • y')
  rw [hkey, smul_comm (B.Q ^ M) B.X y', hy']
end Formalism.CoboundaryTransfers
