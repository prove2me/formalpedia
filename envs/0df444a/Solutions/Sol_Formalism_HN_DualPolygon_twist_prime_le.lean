-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_prime_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:16.326618+00:00
-- url     : https://prove2.me/submissions/d99e7998-a4ae-48ed-82b9-bb0d411b69a5

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
attribute [local instance] Ideal.Quotient.field
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (X : Submodule (𝓞 K) W) (hX : X.FG) (𝔭 : Ideal (𝓞 K))
    [h𝔭 : 𝔭.IsMaximal] (h0 : 𝔭 ≠ ⊥) :
    (𝔭 • X).toAddSubgroup.relIndex X.toAddSubgroup ≤
      Ideal.absNorm 𝔭 ^ finrank K (Submodule.span K (X : Set W)) := by
  change Nat.card (X ⧸ (𝔭 • X).comap X.subtype) ≤ _
  let e : (X ⧸ (𝔭 • X).comap X.subtype) ≃ₗ[𝓞 K] (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Submodule.quotEquivOfEq _ _ (Submodule.map_injective_of_injective X.injective_subtype
      (by simp [Submodule.smul_le_right]))
  rw [Nat.card_congr e.toEquiv]
  have : Module.Finite (𝓞 K) X := Module.Finite.iff_fg.mpr hX
  have : Finite (𝓞 K ⧸ 𝔭) := (Ideal.absNorm_ne_zero_iff 𝔭).1
    (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  have : Module.Finite (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) :=
    Module.Finite.of_restrictScalars_finite (𝓞 K) _ _
  have : Finite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := Module.finite_of_finite (𝓞 K ⧸ 𝔭)
  have hcard : Nat.card (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) =
      Nat.card (𝓞 K ⧸ 𝔭) ^ finrank (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X))) := by
    haveI := Fintype.ofFinite (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
    haveI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hN : Nat.card (𝓞 K ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard, hN]
  apply Nat.pow_le_pow_right (Nat.pos_of_ne_zero (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h)))
  let B := Module.finBasis (𝓞 K ⧸ 𝔭) (X ⧸ (𝔭 • (⊤ : Submodule (𝓞 K) X)))
  have hsurj := Submodule.mkQ_surjective (𝔭 • (⊤ : Submodule (𝓞 K) X))
  choose b' hb' using fun i => hsurj (B i)
  have hli : LinearIndependent (𝓞 K ⧸ 𝔭)
      ((Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b') := by
    have : (Submodule.mkQ (𝔭 • (⊤ : Submodule (𝓞 K) X))) ∘ b' = B := funext hb'
    rw [this]; exact B.linearIndependent
  have hRS : RingHom.ker (algebraMap (𝓞 K) (𝓞 K ⧸ 𝔭)) ≠ ⊤ := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact h𝔭.ne_top
  have hli2 := Ideal.FinrankQuotientMap.linearIndependent_of_nontrivial K hRS X.subtype
    X.injective_subtype (Submodule.mkQ _) hli
  let g : Fin _ → Submodule.span K (X : Set W) :=
    fun i => ⟨(b' i : W), Submodule.subset_span (b' i).2⟩
  have hg : LinearIndependent K g := by
    apply LinearIndependent.of_comp (Submodule.span K (X : Set W)).subtype
    exact hli2
  simpa using hg.fintype_card_le_finrank
end Formalism.HN.DualPolygon
