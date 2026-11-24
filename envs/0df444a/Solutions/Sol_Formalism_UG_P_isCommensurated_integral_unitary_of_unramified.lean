-- Prove2me | solution 1 for Formalism.UG.P.isCommensurated_integral_unitary_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:15.003257+00:00
-- url     : https://prove2.me/submissions/997d5b02-324e-4848-ad7f-01e171b3074a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Theorems.Thm_Formalism_UG_P_glint_exists_denom
import Theorems.Thm_Formalism_UG_P_glint_finite_quotient_of_dvr
import Theorems.Thm_Formalism_UG_P_glint_princ_le_map_conj
import Theorems.Thm_Formalism_UG_P_glint_princ_relIndex_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by
  obtain ⟨-, -, -, hvϖ, -, hq2, hq⟩ := hU
  set A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring with hA
  haveI : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
    isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
      (MulEquiv.surjective _)
  have h0 : Valued.v ϖ ≠ 0 := by rw [hvϖ]; exact WithZero.coe_ne_zero
  haveI : Nontrivial ↥(MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))).valueGroup := by
    refine ⟨⟨1, ⟨Units.mk0 (Valued.v ϖ) h0, MonoidWithZeroHom.mem_valueGroup _ ⟨ϖ, rfl⟩⟩, ?_⟩⟩
    intro h
    have h1 := congrArg (fun u : ↥(MonoidWithZeroHom.ofClass
      (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))).valueGroup =>
        ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_mk0, hvϖ] at h1
    have h2 := WithZero.coe_injective (h1.symm.trans WithZero.coe_one.symm)
    exact absurd (Multiplicative.ofAdd.injective (h2.trans ofAdd_zero.symm)) (by norm_num)
  haveI hD : IsDiscreteValuationRing ↥A.toSubring := Valuation.valuationSubring_isDiscreteValuationRing _
  have hRes : Finite (IsLocalRing.ResidueField ↥A.toSubring) := by
    apply Nat.finite_of_card_ne_zero
    rw [show Nat.card (IsLocalRing.ResidueField ↥A.toSubring) = q ^ 2 from hq]
    exact pow_ne_zero 2 (by omega)
  intro g
  obtain ⟨c, hc0, hg1, hg2⟩ := Formalism.UG.P.glint_exists_denom A (g : GL (Fin n) L)
  haveI : Finite (↥A.toSubring ⧸ Ideal.span {c * c}) :=
    glint_finite_quotient_of_dvr hRes _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact mul_ne_zero hc0 hc0)
  have hO : intL L = A.toSubring := rfl
  unfold KU
  rw [hO]
  have hK : intPts A.toSubring.subtype (GU σ n) = GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range := rfl
  rw [hK]
  have hmap : ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).subgroupOf (GU σ n)).map (MulAut.conj g).toMonoidHom =
      ((GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom).subgroupOf (GU σ n) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy.1⟩, hy, Subtype.ext (by simpa using hyx)⟩
  rw [hmap, Subgroup.relIndex_subgroupOf inf_le_left]
  have hPB := glint_princ_relIndex_ne_zero (n := Fin n) A.toSubring (Ideal.span {c * c})
  have h1 : (princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n).relIndex
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range) ≠ 0 := by
    rw [inf_comm (GU σ n) (bc (n := Fin n) A.toSubring.subtype).range]
    exact Subgroup.relIndex_inter_ne_zero hPB (GU σ n)
  have hle : princ (n := Fin n) A.toSubring.subtype (Ideal.span {c * c}) ⊓ GU σ n ≤
      (GU σ n ⊓ (bc (n := Fin n) A.toSubring.subtype).range).map (MulAut.conj (g : GL (Fin n) L)).toMonoidHom := by
    rintro h ⟨hP, hHh⟩
    obtain ⟨b, hb, hbh⟩ := glint_princ_le_map_conj A.toSubring (g : GL (Fin n) L) c hg1 hg2 hP
    refine ⟨b, ⟨?_, hb⟩, hbh⟩
    have hbe : b = (g : GL (Fin n) L)⁻¹ * h * g := by
      rw [← hbh]
      simp [MulAut.conj_apply, mul_assoc]
    rw [hbe]
    exact (GU σ n).mul_mem ((GU σ n).mul_mem ((GU σ n).inv_mem g.2) hHh) g.2
  exact fun hz => h1 (Subgroup.relIndex_eq_zero_of_le_left hle hz)
end Formalism.UG.P
