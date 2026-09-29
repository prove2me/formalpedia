-- Prove2me | solution 1 for CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5c96bdb7-573f-5692-8c7d-54079e9d61d8

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableT
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus

set_option autoImplicit false

open scoped MatrixGroups ModularForm

private theorem slash_eq_smul_of_hasNebentypus {M : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ M}
    {g : CuspForm (CongruenceSubgroup.Gamma1 M) k} (hg : CuspForm.HasNebentypus ε g)
    (A : SL(2, ℤ)) (hA0 : A ∈ CongruenceSubgroup.Gamma0 M) :
    (⇑g) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ)) = ε ((A 1 1 : ℤ) : ZMod M) • ⇑g := by
  funext τ
  show ((⇑g) ∣[k] A) τ = _
  rw [ModularForm.SL_slash_apply, hg A hA0 τ, Pi.smul_apply, smul_eq_mul]
  have hden : UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ =
      ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) := by
    simp [UpperHalfPlane.denom]
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ _
  rw [hden, mul_assoc, mul_assoc, mul_comm (_ ^ k), mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero,
    mul_one]

theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hfg : (⇑f : UpperHalfPlane → ℂ) = ⇑g) (hg : CuspForm.HasNebentypus ε g) :
    (∀ d : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ε (d : ZMod M) • ⇑g) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (⇑(CuspForm.heckeTLinH k hℓ hℓM f) : UpperHalfPlane → ℂ) =
        ModularForm.heckeU k ℓ ⇑g + ε (ℓ : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix ℓ)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M →
      (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑g) := by
  refine ⟨fun d => ?_, fun ℓ hℓ hℓM => ?_, fun q hq hqM => ?_⟩
  · rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) d f, hfg,
      slash_eq_smul_of_hasNebentypus hg _ (CuspForm.gammaLift M d).2]
    congr 2
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (CuspForm.gamma0Units_gammaLift (M := M) d)
    simp only [CohCarrier.val_gamma0Units] at this
    exact this
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    rw [CuspForm.coe_heckeTLinH_apply k hℓ hℓM (CuspForm.stableT M H k hℓ hℓM) f, hfg, SlashAction.slash_mul,
      slash_eq_smul_of_hasNebentypus hg _ (CuspForm.gammaLift M _).2, CuspForm.gammaLift_apply_11 hℓ hℓM]
    congr 1
    simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply]
  · rw [CuspForm.coe_heckeULinH_apply k (CuspForm.stableU M H k hq hqM) f, hfg]

end S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
end P2MW
export P2MW.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus (solution)
