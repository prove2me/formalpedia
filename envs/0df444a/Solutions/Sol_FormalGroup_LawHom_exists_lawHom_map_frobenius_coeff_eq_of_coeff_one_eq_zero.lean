-- Prove2me | solution 1 for FormalGroup.LawHom.exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5e2c9f72-7920-5578-b679-5e1e4325f314

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

import Definitions.Def_MvFormalGroup_OfFormalGroupV2
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

namespace QuotIsoAux

open MvPowerSeries

theorem expand_injective {σ R : Type*} [CommRing R] (p : ℕ) (hp : p ≠ 0) :
    Function.Injective (MvPowerSeries.expand p hp : MvPowerSeries σ R → MvPowerSeries σ R) := by
  intro f g h
  ext m
  rw [← MvPowerSeries.coeff_expand_smul p hp f m, ← MvPowerSeries.coeff_expand_smul p hp g m, h]

end QuotIsoAux

open MvPowerSeries

theorem solution
    {S : Type u} [CommRing S] (q : ℕ) [Fact q.Prime] [CharP S q]
    {F G : FormalGroup S} (θ : FormalGroup.LawHom F G) (h1 : PowerSeries.coeff 1 θ.series = 0) :
    ∃ θ₁ : FormalGroup.LawHom (F.map (frobenius S q)) G,
      ∀ n : ℕ, PowerSeries.coeff n θ₁.series = PowerSeries.coeff (q * n) θ.series := by
  classical
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  set s := θ.series with hs_def
  have hs0 : PowerSeries.constantCoeff s = 0 := θ.constantCoeff_series

  have hvan : ∀ n : ℕ, ¬ q ∣ n → PowerSeries.coeff n s = 0 := by
    intro n hn
    have hlin : MvFormalGroup.linearPart θ.toMvHom.toPowerSeries = 0 := by
      show MvFormalGroup.linearPart (fun _ : Fin 1 => MvFormalGroup.toMv θ.series) = 0
      rw [MvFormalGroup.linearPart_toMv, h1, zero_smul]
    have h := MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP q
      (MvFormalGroup.ofFormalGroup F) (MvFormalGroup.ofFormalGroup G) θ.toMvHom.toPowerSeries
      θ.toMvHom.constantCoeff_eq_zero hlin θ.toMvHom.subst_eq 0 (Finsupp.single 0 n)
      ⟨0, by rwa [Finsupp.single_eq_same]⟩
    rwa [FormalGroup.LawHom.toMvHom_toPowerSeries, MvFormalGroup.coeff_toMv] at h

  let s₁ : PowerSeries S := PowerSeries.mk fun n => PowerSeries.coeff (q * n) s
  have hs₁ : ∀ n, PowerSeries.coeff n s₁ = PowerSeries.coeff (q * n) s := fun n => PowerSeries.coeff_mk _ _
  have hexp : PowerSeries.expand q hq0 s₁ = s := by
    ext m
    rw [PowerSeries.coeff_expand]
    split_ifs with hm
    · rw [hs₁, Nat.mul_div_cancel' hm]
    · exact (hvan m hm).symm
  have hsub : s = PowerSeries.subst (PowerSeries.X ^ q : PowerSeries S) s₁ := by
    rw [← hexp, PowerSeries.expand_apply]
  have hs₁0 : PowerSeries.constantCoeff s₁ = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hs₁, mul_zero,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0]

  have hXq : PowerSeries.HasSubst (PowerSeries.X ^ q : PowerSeries S) := PowerSeries.HasSubst.X_pow hq0
  have hF : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hF' : PowerSeries.HasSubst (F.map (frobenius S q)).toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero (F.map (frobenius S q)).zero_constantCoeff
  have hXi : ∀ i : Fin 2, PowerSeries.HasSubst (X i : MvPowerSeries (Fin 2) S) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X i)
  have hsX : ∀ (t : PowerSeries S), PowerSeries.constantCoeff t = 0 →
      HasSubst (![FormalGroup.LawHom.substX 0 t, FormalGroup.LawHom.substX 1 t] :
        Fin 2 → MvPowerSeries (Fin 2) S) := by
    intro t ht
    refine hasSubst_of_constantCoeff_zero (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
    · unfold FormalGroup.LawHom.substX
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X _) t ht

  have hFq : MvPowerSeries.expand q hq0 (F.map (frobenius S q)).toPowerSeries = F.toPowerSeries ^ q := by
    rw [FormalGroup.map_toPowerSeries, ← MvPowerSeries.map_expand, MvPowerSeries.map_frobenius_expand]
  have comm₁ : PowerSeries.subst (F.map (frobenius S q)).toPowerSeries s₁ =
      MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s₁, FormalGroup.LawHom.substX 1 s₁] G.toPowerSeries := by
    apply QuotIsoAux.expand_injective q hq0

    have eL : MvPowerSeries.expand q hq0 (PowerSeries.subst (F.map (frobenius S q)).toPowerSeries s₁) =
        PowerSeries.subst F.toPowerSeries s := by
      rw [PowerSeries.subst, MvPowerSeries.expand_subst q hq0 (PowerSeries.HasSubst.const hF'), hFq,
        hsub, PowerSeries.subst_comp_subst_apply hXq hF, PowerSeries.subst_pow hF, PowerSeries.subst_X hF]
      rfl

    have eX : ∀ i : Fin 2, MvPowerSeries.expand q hq0 (FormalGroup.LawHom.substX i s₁) =
        FormalGroup.LawHom.substX i s := by
      intro i
      unfold FormalGroup.LawHom.substX
      rw [PowerSeries.expand_subst q hq0 (hXi i), hsub, PowerSeries.subst_comp_subst_apply hXq (hXi i),
        PowerSeries.subst_pow (hXi i), PowerSeries.subst_X (hXi i), MvPowerSeries.expand_X]
    have eR : MvPowerSeries.expand q hq0
        (MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s₁, FormalGroup.LawHom.substX 1 s₁] G.toPowerSeries) =
        MvPowerSeries.subst ![FormalGroup.LawHom.substX 0 s, FormalGroup.LawHom.substX 1 s] G.toPowerSeries := by
      rw [MvPowerSeries.expand_subst q hq0 (hsX s₁ hs₁0)]
      congr 1
      funext i
      fin_cases i
      · exact eX 0
      · exact eX 1
    rw [eL, eR]
    exact θ.comm
  exact ⟨⟨s₁, hs₁0, comm₁⟩, hs₁⟩

end S_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero
end P2MW
export P2MW.S_FormalGroup_LawHom_exists_lawHom_map_frobenius_coeff_eq_of_coeff_one_eq_zero (solution)
