-- Prove2me | solution 1 for CerednikDrinfeld.jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a75e67b7-ddb9-5fdf-8212-960ca2ae285c

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Theorems.Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin
import Theorems.Thm_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne

set_option autoImplicit false

open scoped TensorProduct Quaternion in
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld in
theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ q) (i : Fin 2)
    (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ) :
    jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) =
      (classSetVertexHecke N Λ R ℓ).mulVecLin (jointDelta (classSetDegeneracyData R n) i x) := by
  classical
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hΛo : QuaternionAlgebra.IsOrder Λ := hΛ.isOrder
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hℓ0 : (ℓ : ℕ) ≠ 0 := ℓ.2.ne_zero
  have hcop : (ℓ : ℕ).Coprime q := (Nat.coprime_primes ℓ.2 Fact.out).mpr hℓ

  obtain ⟨m, τ, hmτ, hδ⟩ : ∃ (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (τ : _ → _),
      ((m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n)) ∧
      jointDelta (classSetDegeneracyData R n) i =
        CerednikDrinfeld.pushforward (fun e : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) =>
          ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) := by
    fin_cases i
    · refine ⟨1, id, Or.inl ⟨rfl, rfl⟩, ?_⟩
      show pushforward (classSetDegeneracyData R n).a = _
      congr 1
      funext e
      simp [classSetDegeneracyData, classSetForget]
    · exact ⟨n, _, Or.inr ⟨rfl, rfl⟩, rfl⟩
  rw [hδ]
  funext v
  simp only [classSetEdgeHecke, classSetVertexHecke, if_neg hℓ]
  by_cases hN : (ℓ : ℕ) ∣ N
  · simp only [if_pos hN]
    exact CerednikDrinfeld.pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin Λ R hΛo hRo hRΛ q ℓ hq0 hℓ0
      hcop n hnH m τ hmτ x v
  · simp only [if_neg hN]
    exact CerednikDrinfeld.pushforward_classSetHeckeMatrix_primeHeckeSet_meetOrder_mulVecLin R hRo q ℓ hq0 hℓ0 hcop n hnH
      m τ hmτ x v

end S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne
end P2MW
export P2MW.S_CerednikDrinfeld_jointDelta_classSetEdgeHecke_mulVecLin_eq_classSetVertexHecke_mulVecLin_jointDelta_of_ne (solution)
