-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.capelli_inequivalence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:31.398984+00:00
-- url     : https://prove2.me/submissions/a8716e06-0263-4d51-ba86-7f40a206a5ed

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_kfin_iff
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_isURepOn_of_ds
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution : Inequiv := by
  intro hE k r ε ε' μ μ' H H' _ _ _ _ _ _ σ σ' hμ hμ' hσ hσ' hne ⟨U, hU⟩
  have hR := isURepOn_of_ds hσ
  have hσ₀ := hσ
  obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS, hst, -, ⟨v, hvS, hv0, -⟩, -⟩, -⟩ := hσ₀
  have hv : IsKFinHpk (k := k) (r := r) σ v := (kfin_iff hP σ v).2 ⟨S, hS, hvS, hst⟩
  have hv' : IsKFinHpk (k := k) (r := r) σ' (U v) := by
    obtain ⟨S₁, hS₁, hv₁, hst₁⟩ := hv
    refine ⟨S₁.map (U.toLinearEquiv : H →ₗ[ℂ] H'), inferInstance, ⟨v, hv₁, rfl⟩, ?_⟩
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, hst₁ g hg x hx, hU g hg.1 x⟩
  let φ : B.Mat k r → ℂ := fun g => ⟪v, σ g v⟫_ℂ
  have h1 : IsCoef k r ε μ φ := ⟨H, _, _, inferInstance, σ, v, v, hμ, hσ, hv, hv, fun _ _ => rfl⟩
  have h2 : IsCoef k r ε' μ' φ := ⟨H', _, _, inferInstance, σ', U v, U v, hμ', hσ', hv', hv', fun g hg => by
    rw [← hU g hg, U.inner_map_map]⟩
  have hone : (1 : B.Mat k r) ∈ B.GV k r := by
    show (1 : B.Mat k r)ᴴ * _ * 1 = _
    simp
  have hφ1 : φ 1 • (1 : ℂ →L[ℂ] ℂ) ≠ 0 := by
    refine smul_ne_zero ?_ one_ne_zero
    simp [φ, hR.1.1, hv0]
  have key : ∀ Y : ℂ, ∏ s, (Y + (μ s : ℂ)) = ∏ s, (Y + (μ' s : ℂ)) := fun Y =>
    smul_left_injective ℂ hφ1 ((hE k r ε μ φ ℂ ℂ 1 h1 Y 1 hone).symm.trans (hE k r ε' μ' φ ℂ ℂ 1 h2 Y 1 hone))
  have sub : ∀ {a b : Fin (2 * r + k + 1) → ℝ}, (∀ Y : ℂ, ∏ s, (Y + (a s : ℂ)) = ∏ s, (Y + (b s : ℂ))) →
      Set.range a ⊆ Set.range b := by
    rintro a b hab _ ⟨s, rfl⟩
    have h0 : ∏ t, (-(a s : ℂ) + (b t : ℂ)) = 0 := by
      rw [← hab]
      exact Finset.prod_eq_zero (Finset.mem_univ s) (by ring)
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨t, ?_⟩
    have : (b t : ℂ) = a s := by linear_combination ht
    exact_mod_cast this
  exact hne ((hμ.1.range_inj hμ'.1).1 (Set.Subset.antisymm (sub key) (sub fun Y => (key Y).symm)))
end CompanionTheory.LimBd.Main
