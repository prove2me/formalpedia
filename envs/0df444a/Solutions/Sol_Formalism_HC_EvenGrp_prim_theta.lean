-- Prove2me | solution 1 for Formalism.HC.EvenGrp.prim_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:00:18.934614+00:00
-- url     : https://prove2.me/submissions/5ceee66f-187c-403d-8da2-a914f0b5c638

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_unitsMap_unitOfCoprime
import Theorems.Thm_Formalism_HC_EvenGrp_theta_toA
import Theorems.Thm_Formalism_HC_EvenGrp_exact
import Theorems.Thm_Formalism_HC_An_Induces_unique
import Theorems.Thm_Formalism_HC_An_induces_of
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_HostRaw_dir_unit
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_prim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)
namespace Formalism.HC.EvenGrp
theorem _root_.solution (χ : DirichletCharacter ℂ M) (hχ : χ ∈ Ξ) :
    PChar.of χ = (host Ξ e hev hH hc he hs).prim (theta Ξ e hev χ hχ) := by
  set H := host Ξ e hev hH hc he hs with hHdef
  refine An.Induces.unique (f := fun a => χ (a : ZMod M)) (M := H.condN * M) (mul_ne_zero H.condN_pos.ne' (NeZero.ne M))
    ⟨(PChar.of χ).prim, fun a ha => (An.induces_of χ).2 a ha.coprime_mul_left_right⟩ ⟨(H.prim _).prim, fun a ha => ?_⟩
  have haN : a.Coprime H.condN := ha.coprime_mul_right_right
  have haM : a.Coprime M := ha.coprime_mul_left_right
  have haW : a.Coprime (Nat.lcm (2 ^ (e + 2)) M) :=
    (Nat.Coprime.mul_right (haN.coprime_dvd_right ((H.tower_dvd.mul_right _).mul_right _)) haM).coprime_dvd_right
      (Nat.lcm_dvd_mul _ _)
  refine ((H.isPrimOf_prim _).2 a haN).trans ?_
  show _ = χ (a : ZMod M)
  rw [HostRaw.dirAt, ← ZMod.coe_unitOfCoprime a haN, H.dir_unit, ← ZMod.coe_unitOfCoprime a haM, ← MulChar.coe_toUnitHom]
  refine congrArg Units.val ?_
  have h1 := theta_toA Ξ e hev χ hχ (H.art (ZMod.unitOfCoprime a haN)).1 (ZMod.unitOfCoprime a haW)
  rw [unitsMap_unitOfCoprime, unitsMap_unitOfCoprime] at h1
  have h2 : (H.art (ZMod.unitOfCoprime a haN)).2 =
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e))) :=
    congrArg (data Ξ e hev).toA (unitsMap_unitOfCoprime ((data Ξ e hev).m_dvd q d) a haN)
  have h3 : H.art (ZMod.unitOfCoprime a haN) = ((H.art (ZMod.unitOfCoprime a haN)).1,
      (data Ξ e hev).toA (ZMod.unitOfCoprime a (haW.coprime_dvd_right (QS_dvd Ξ e)))) := Prod.ext rfl h2
  exact (congrArg (theta Ξ e hev χ hχ) h3).trans h1
end Formalism.HC.EvenGrp
