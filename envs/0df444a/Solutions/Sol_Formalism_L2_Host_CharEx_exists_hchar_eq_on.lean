-- Prove2me | solution 1 for Formalism.L2.Host.CharEx.exists_hchar_eq_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:03.427089+00:00
-- url     : https://prove2.me/submissions/22022e75-4d04-41ee-843f-c68e1507aade

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharExGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.L2.Host.CharEx
variable (L : Type) [Field L] [NumberField L]
variable {L}
namespace Formalism.L2.Host.CharEx
theorem _root_.solution (hD : DivExtC) (hO : OpenUnits L) (M : Subgroup (Ideles L)) (hM : unitIdeles L ≤ M)
    (Φ : Ideles L →* ℂˣ) (hΦ : Continuous Φ) (h1 : ∀ k : Lˣ, diagUnits L k ∈ M → Φ (diagUnits L k) = 1) :
    ∃ χ : HChar L, ∀ m ∈ M, χ.1 m = Φ m := by
  set D : Subgroup (Ideles L) := (diagUnits L).range
  let K0 : Subgroup M := D.comap M.subtype
  have hK : K0 ≤ (Φ.comp M.subtype).ker := by
    intro x hx
    have hx' : (x : Ideles L) ∈ (diagUnits L).range := hx
    obtain ⟨k, hk⟩ := hx'
    have hkM : diagUnits L k ∈ M := hk ▸ x.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hk]
    exact h1 k hkM
  let φ1 : M ⧸ K0 →* ℂˣ := QuotientGroup.lift K0 (Φ.comp M.subtype) hK
  let ι : M ⧸ K0 →* Ideles L ⧸ D := QuotientGroup.map K0 D M.subtype le_rfl
  have hι : Function.Injective ι := by
    refine (injective_iff_map_eq_one ι).mpr fun a ha => ?_
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at ha
      exact (QuotientGroup.eq_one_iff x).mpr ha
  let e : M ⧸ K0 ≃* ι.range := MonoidHom.ofInjective hι
  let g : ι.range →* ℂˣ := φ1.comp e.symm.toMonoidHom
  obtain ⟨g', hg'⟩ := hD (Ideles L ⧸ D) ι.range g
  let χ0 : Ideles L →* ℂˣ := g'.comp (QuotientGroup.mk' D)
  have hχM : ∀ m ∈ M, χ0 m = Φ m := by
    intro m hm
    have hq : ((e (QuotientGroup.mk ⟨m, hm⟩) : ι.range) : Ideles L ⧸ D) = (m : Ideles L ⧸ D) := by
      rw [MonoidHom.ofInjective_apply]
      rfl
    have h2 := hg' (e (QuotientGroup.mk ⟨m, hm⟩))
    rw [hq] at h2
    change g' (m : Ideles L ⧸ D) = Φ m
    rw [h2]
    simp [g, φ1]
  have hcont : Continuous χ0 := by
    refine continuous_of_continuousAt_one χ0 ?_
    have hev : Φ =ᶠ[nhds 1] χ0 := by
      filter_upwards [hO.mem_nhds (unitIdeles L).one_mem] with x hx
      exact (hχM x (hM hx)).symm
    exact hΦ.continuousAt.congr hev
  have hdiag : ∀ k : Lˣ, χ0 (diagUnits L k) = 1 := by
    intro k
    have hmem : diagUnits L k ∈ D := ⟨k, rfl⟩
    change g' (QuotientGroup.mk' D (diagUnits L k)) = 1
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hmem, map_one]
  exact ⟨⟨χ0, hcont, hdiag⟩, hχM⟩
end Formalism.L2.Host.CharEx
