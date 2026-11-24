-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_newton
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:12.477675+00:00
-- url     : https://prove2.me/submissions/23dc4e38-4e78-4671-b6f2-5e651c559513

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Newton_step
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_add
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_pow_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H) (hHS : Ent S H)
    (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K)) (hk : e + 1 ≤ k)
    {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z) (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) (N : ℕ) :
    ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ N • Z' := by
  have key : ∀ j : ℕ, ∃ D Z' : Matrix n n K, Ent S D ∧ Ent S Z' ∧
      (X + ϖ ^ (k - e) • D)ᴴ * H * (X + ϖ ^ (k - e) • D) = H + ϖ ^ (k + j) • Z' := by
    intro j
    induction j with
    | zero => exact ⟨0, Z, Ent.zero, hZ, by simpa using hXZ⟩
    | succ j ih =>
      obtain ⟨D, Z', hD, hZ', hEq⟩ := ih
      obtain ⟨D₁, Z'', hD₁, hZ'', hEq'⟩ := Newton.step hS hH hES hHE (by omega : e + 1 ≤ k + j)
        (hX.add (Ent.smul (S.pow_mem hS.mem _) hD)) hZ' hEq
      refine ⟨D + ϖ ^ j • D₁, Z'', hD.add (Ent.smul (S.pow_mem hS.mem _) hD₁), hZ'', ?_⟩
      have e1 : X + ϖ ^ (k - e) • (D + ϖ ^ j • D₁) =
          X + ϖ ^ (k - e) • D + ϖ ^ (k + j - e) • D₁ := by
        rw [smul_add, smul_smul, ← pow_add, add_assoc, show k - e + j = k + j - e by omega]
      rw [e1, hEq', show k + (j + 1) = k + j + 1 by omega]
  obtain ⟨D, Z', hD, hZ', hEq⟩ := key N
  refine ⟨D, ϖ ^ k • Z', hD, Ent.smul (S.pow_mem hS.mem _) hZ', ?_⟩
  rw [hEq, smul_smul, ← pow_add, add_comm k N]
end Formalism.HermitianLattices.Ext.L3.HU
