-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.isFD_of_SF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:10.825836+00:00
-- url     : https://prove2.me/submissions/29884179-cc26-4e49-8d8c-f8ddd5ba7fde

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] {Ω : Set G} (hΩ : SF (Γ : Set G) Ω) (μ : Measure G) :
    IsFundamentalDomain Γ Ω μ := by
  have key : ∀ x : G, ∃! g : Γ, g • x ∈ Ω := by
    intro x
    obtain ⟨s, hs, hsx⟩ := hΩ.2.1 x
    refine ⟨⟨s, hs⟩, hsx, ?_⟩
    rintro ⟨t, ht⟩ htx
    have htx' : t * x ∈ Ω := htx
    have h1 : (t * s⁻¹) * (s * x) ∈ Ω := by simpa [mul_assoc] using htx'
    have h2 : t * s⁻¹ = 1 := hΩ.2.2 (s * x) hsx (t * s⁻¹) (Γ.mul_mem ht (Γ.inv_mem hs)) h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  first
  | exact IsFundamentalDomain.mk' hΩ.1.nullMeasurableSet key
  | exact
      { nullMeasurableSet := hΩ.1.nullMeasurableSet
        ae_covers := ae_of_all _ fun x => (key x).exists
        aedisjoint := fun a b hab => Disjoint.aedisjoint (Set.disjoint_left.2 fun y hya hyb => by
          obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hya
          obtain ⟨v, hv, hvu⟩ := Set.mem_smul_set.1 hyb
          have e1 : (b⁻¹ * a) • u ∈ Ω := by rw [mul_smul, ← hvu, inv_smul_smul]; exact hv
          have e2 : (1 : Γ) • u ∈ Ω := by rw [one_smul]; exact hu
          have := (key u).unique e1 e2
          exact hab (by rw [inv_mul_eq_one] at this; exact this.symm)) }
end Formalism.L2.SG.MeasureShiftInvariance
