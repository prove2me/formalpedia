-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.lift_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:32.43239+00:00
-- url     : https://prove2.me/submissions/b52b781f-1031-4bc8-a0bc-12ee4a39159f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_coe_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_isUnit_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_phi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x2.coe_phi

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (x : GL (Idx r k) o) (nb : GL (Idx r k) 𝔽) (hb : GL (Fin k) 𝔽)
    (hn : IsN (nb : Matrix (Idx r k) (Idx r k) 𝔽)) (hx : red o (Idx r k) x = nb * phi 𝔽 r k hb) :
    ∃ (n κ : GL (Idx r k) o) (h : GL (Fin k) o), IsN (n : Matrix (Idx r k) (Idx r k) o) ∧
      red o (Fin k) h = hb ∧ κ ∈ (red o (Idx r k)).ker ∧ x = n * phi o r k h * κ := by
  obtain ⟨h, rfl⟩ := red_surjective o (Fin k) hb
  let n0 : Matrix (Idx r k) (Idx r k) o := Matrix.of fun i j =>
    if cI r k j ≤ cI r k i then (1 : Matrix (Idx r k) (Idx r k) o) i j
    else Function.surjInv IsLocalRing.residue_surjective ((nb : Matrix (Idx r k) (Idx r k) 𝔽) i j)
  have hU : IsUc (cI r k) n0 := by
    intro i j hij
    simp [n0, hij]
  have hN : IsN n0 := (isN_iff _).2 hU
  have hmap : n0.map (IsLocalRing.residue o) = (nb : Matrix (Idx r k) (Idx r k) 𝔽) := by
    ext i j
    by_cases hij : cI r k j ≤ cI r k i
    · rw [(hU.map (IsLocalRing.residue o)) i j hij, (isN_iff _).1 hn i j hij]
    · simp [n0, hij, Function.surjInv_eq]
  let n : GL (Idx r k) o := toGL n0 (isN_isUnit_det hN)
  have hred : red o (Idx r k) n = nb := Units.ext hmap
  refine ⟨n, (n * phi o r k h)⁻¹ * x, h, hN, rfl, ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hred, red_phi, hx]
  group
end Formalism.FourierDecayAlt.P.S3x2
