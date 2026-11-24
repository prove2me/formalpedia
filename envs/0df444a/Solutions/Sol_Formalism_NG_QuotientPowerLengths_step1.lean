-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.step1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:43:09.585061+00:00
-- url     : https://prove2.me/submissions/3e83174d-3049-4572-8cd0-e5ab1baa96b6

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_mem_smulRange
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_length_quot_smulRange_free
import Theorems.Thm_Formalism_NG_QuotientPowerLengths_isTorsionFree_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution (N : Submodule O V) (hN : N.FG) (W U : Submodule (FractionRing O) V)
    (hNWU : N ≤ (W ⊔ U).restrictScalars O) (l : O) :
    Module.length O (N ⧸ (smulRange N l ⊔
      LinearMap.ker ((U.mkQ.restrictScalars O) ∘ₗ N.subtype))) ≤
      (finrank (FractionRing O) W : ℕ∞) * addVal O l := by
  set g : N →ₗ[O] V ⧸ U := (U.mkQ.restrictScalars O) ∘ₗ N.subtype with hg
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Finite O (LinearMap.range g) := by
    first
      | exact Module.Finite.range g
      | infer_instance
  haveI hQtf : IsTorsionFree O (LinearMap.range g) :=
    ⟨fun r hr x y hxy => Subtype.ext ((isTorsionFree_quot U).1 hr (congrArg Subtype.val hxy))⟩
  have hlenQ := length_quot_smulRange_free (LinearMap.range g) l
  have hle : smulRange N l ⊔ LinearMap.ker g ≤
      LinearMap.ker ((smulRange (LinearMap.range g) l).mkQ ∘ₗ g.rangeRestrict) := by
    refine sup_le ?_ ?_
    · intro m hm
      obtain ⟨n, rfl⟩ := (mem_smulRange l m).mp hm
      rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact (mem_smulRange l _).mpr ⟨_, rfl⟩
    · intro m hm
      rw [LinearMap.mem_ker] at hm ⊢
      rw [LinearMap.comp_apply]
      have h0 : g.rangeRestrict m = 0 := Subtype.ext hm
      rw [h0, map_zero]
  have hker : LinearMap.ker ((smulRange (LinearMap.range g) l).mkQ ∘ₗ g.rangeRestrict) ≤
      smulRange N l ⊔ LinearMap.ker g := by
    intro n hn
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hn
    obtain ⟨q, hq⟩ := (mem_smulRange l _).mp hn
    obtain ⟨n', hn'⟩ := LinearMap.surjective_rangeRestrict g q
    have hsplitn : n = l • n' + (n - l • n') := by abel
    rw [hsplitn]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ((mem_smulRange l _).mpr ⟨n', rfl⟩))
      (Submodule.mem_sup_right ?_)
    rw [LinearMap.mem_ker, map_sub, map_smul]
    have h1 : g n' = (q : V ⧸ U) := congrArg Subtype.val hn'
    have h2 : g n = ((l • q : LinearMap.range g) : V ⧸ U) := (congrArg Subtype.val hq).symm
    rw [h1, h2, Submodule.coe_smul, sub_self]
  have hψ : Function.Injective ((smulRange N l ⊔ LinearMap.ker g).liftQ _ hle) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective _ z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hker hz
  have hd := Module.length_le_of_injective _ hψ
  have he : finrank O (LinearMap.range g) ≤ finrank (FractionRing O) W := by
    haveI : NoZeroSMulDivisors O (LinearMap.range g) := by
      refine ⟨fun {c x} h => ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hreg : IsRegular c := isRegular_of_ne_zero hc
        apply hQtf.1 hreg
        show c • x = c • 0
        rw [h, smul_zero]
    haveI : Module.Free O (LinearMap.range g) := by
      first
        | exact Module.free_of_finite_type_torsion_free'
        | infer_instance
    let b := Module.Free.chooseBasis O (LinearMap.range g)
    have hmem : ∀ i, ((b i : LinearMap.range g) : V ⧸ U) ∈ W.map U.mkQ := by
      intro i
      obtain ⟨n, hn⟩ := LinearMap.mem_range.mp (b i).2
      rw [← hn, Submodule.mem_map]
      have hnWU : (n : V) ∈ W ⊔ U := hNWU n.2
      obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hnWU
      refine ⟨a, ha, ?_⟩
      have hc0 : U.mkQ c = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hc
      show U.mkQ a = U.mkQ (n : V)
      rw [← hac, map_add, hc0, add_zero]
    have hli : LinearIndependent O (fun i => ((b i : LinearMap.range g) : V ⧸ U)) :=
      b.linearIndependent.map' (LinearMap.range g).subtype (Submodule.ker_subtype _)
    have hliK := (LinearIndependent.iff_fractionRing O (FractionRing O)).mp hli
    have hliW : LinearIndependent (FractionRing O) (fun i => (⟨_, hmem i⟩ : W.map U.mkQ)) :=
      LinearIndependent.of_comp (W.map U.mkQ).subtype hliK
    calc finrank O (LinearMap.range g)
        = Fintype.card (Module.Free.ChooseBasisIndex O (LinearMap.range g)) := by
          first
            | exact Module.finrank_eq_card_chooseBasisIndex O _
            | exact Module.finrank_eq_card_chooseBasisIndex
            | simp [Module.finrank_eq_card_chooseBasisIndex]
      _ ≤ finrank (FractionRing O) (W.map U.mkQ) := hliW.fintype_card_le_finrank
      _ ≤ finrank (FractionRing O) W := Submodule.finrank_map_le _ _
  calc Module.length O (N ⧸ (smulRange N l ⊔ LinearMap.ker g))
      ≤ Module.length O ((LinearMap.range g) ⧸ smulRange (LinearMap.range g) l) := hd
    _ = (finrank O (LinearMap.range g) : ℕ∞) * addVal O l := hlenQ
    _ ≤ (finrank (FractionRing O) W : ℕ∞) * addVal O l := by
        first
          | gcongr
          | exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr he) (zero_le _)
end Formalism.NG.QuotientPowerLengths
