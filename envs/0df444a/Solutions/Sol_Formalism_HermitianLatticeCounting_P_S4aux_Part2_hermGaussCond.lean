-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.hermGaussCond
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.001862+00:00
-- url     : https://prove2.me/submissions/06f6955e-e705-4875-9e9c-77883a066b30

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H1 : HermGaussRing) (H2 : AnnihSize) : HermGaussCond := by
  intro o O S _ _ _ _ _ _ _ _ _ ϖ pr τ ψ q N i n Gm φ hU hϖ hq hq2 hsur hker _ hiN hτ hψ hG hφ1 hφ
  have A := H2 o O S ϖ pr τ ψ q N i hU hϖ hq hq2 hsur hker hiN hτ hψ
  have B := H1 S n Gm ψ φ hG hφ1 hφ
  rw [A.2] at B
  have hS : (Fintype.card S : ℝ) = (q : ℝ) ^ (2 * N) := by
    rw [← Nat.card_eq_fintype_card, A.1]; push_cast; rfl
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [hS] at B ⊢
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hiN
  rw [Nat.add_sub_cancel_left] at B
  have e : ((q : ℝ) ^ (i * n))⁻¹ * ((q : ℝ) ^ (2 * (i + m))) ^ n = (q : ℝ) ^ ((i + 2 * m) * n) := by
    rw [← pow_mul, inv_mul_eq_div, div_eq_iff (by positivity), ← pow_add]; congr 1; ring
  rw [e]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (B.trans (le_of_eq ?_))
  push_cast
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
