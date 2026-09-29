-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/085c1f12-949c-592e-9514-70d4cd912c49

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_isDrinfeldBasisAdic_zero_zero_iff
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_FormalGroup_exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot
import Theorems.Thm_FormalGroup_coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

universe u

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hγ : PowerSeries.coeff 1 (PowerSeries.coeff q (Fu.nthSeries q)) - 1 ∈ maximalIdeal W₀) :
    ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
      (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
      (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) → (maximalIdeal T) ^ 2 = ⊥ → (q : T) = 0 →
      ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
          (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
          ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
            ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
  intro T _ _ _ _ resT hresT hkerT hresT₀ hsq hqT G _ hG
  classical

  haveI hIT : IsAdicComplete (maximalIdeal T) T := by
    have hpow : ∀ n, 2 ≤ n → (maximalIdeal T ^ n • ⊤ : Submodule T T) = ⊥ := by
      intro n hn
      have : maximalIdeal T ^ n = ⊥ := le_bot_iff.mp (hsq ▸ Ideal.pow_le_pow_right hn)
      rw [this]; simp
    haveI : IsHausdorff (maximalIdeal T) T := ⟨fun x hx => by
      have := hx 2
      rw [hpow 2 le_rfl, SModEq.bot] at this
      exact this⟩
    haveI : IsPrecomplete (maximalIdeal T) T := ⟨fun f hf => by
      refine ⟨f 2, fun n => ?_⟩
      rcases le_or_gt n 2 with hn | hn
      · exact (hf hn)
      · have h2 := hf hn.le
        rw [hpow 2 le_rfl, SModEq.bot] at h2
        rw [h2]⟩
    exact ⟨⟩
  have hmemT : ∀ x : T, x ∈ maximalIdeal T ↔ resT x = 0 := fun x => by rw [← hkerT, RingHom.mem_ker]
  have hsqz : ∀ x : T, x ∈ maximalIdeal T → x * x = 0 := fun x hx => by
    have : x * x ∈ maximalIdeal T ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rwa [hsq, Ideal.mem_bot] at this

  have hW₀T : ∀ w : W₀, w ∈ maximalIdeal W₀ → algebraMap W₀ T w = 0 := by
    intro w hw
    rw [hW₀, Ideal.mem_span_singleton] at hw
    obtain ⟨y, rfl⟩ := hw
    rw [map_mul, map_natCast, hqT, zero_mul]

  have hkerle : RingHom.ker res₀ ≤ RingHom.ker (algebraMap W₀ T) := by
    intro w hw; rw [RingHom.mem_ker]; exact hW₀T w (hker₀ ▸ hw)
  have hH : ∀ a ∈ RingHom.ker res₀, algebraMap W₀ T a = 0 := fun w hw => hW₀T w (hker₀ ▸ hw)
  let ι : k →+* T := (Ideal.Quotient.lift (RingHom.ker res₀) (algebraMap W₀ T) hH).comp
    (RingHom.quotientKerEquivOfSurjective hres₀).symm.toRingHom
  have hι : ∀ w : W₀, ι (res₀ w) = algebraMap W₀ T w := by
    intro w
    show Ideal.Quotient.lift (RingHom.ker res₀) (algebraMap W₀ T) hH
      ((RingHom.quotientKerEquivOfSurjective hres₀).symm (res₀ w)) = _
    have : (RingHom.quotientKerEquivOfSurjective hres₀).symm (res₀ w) = Ideal.Quotient.mk _ w := by
      apply (RingHom.quotientKerEquivOfSurjective hres₀).injective
      rw [RingEquiv.apply_symm_apply]; rfl
    rw [this, Ideal.Quotient.lift_mk]
  letI : Algebra k T := ι.toAlgebra
  have hresι : ∀ a : k, resT (algebraMap k T a) = a := by
    intro a; obtain ⟨w, rfl⟩ := hres₀ a
    show resT (ι (res₀ w)) = res₀ w
    rw [hι, hresT₀]

  haveI : IsAdicComplete (⊥ : Ideal k) k := inferInstance
  obtain ⟨u₀, hu₀, hqF₀⟩ := (FormalGroup.isDrinfeldBasisAdic_zero_zero_iff (⊥ : Ideal k) F₀ q).mp hF₀
  have hqlt : q < q * q := by nlinarith [(Fact.out : q.Prime).two_le]
  set γ : PowerSeries W₀ := PowerSeries.coeff q (Fu.nthSeries q) with hγdef
  have hγ₀ : PowerSeries.constantCoeff γ ∈ maximalIdeal W₀ := by
    rw [← hker₀, RingHom.mem_ker]
    have h := FormalGroup.IsBaseChange.nthSeries_eq_map Fu
      (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀ hFu q
    have := congrArg (PowerSeries.coeff q) h
    rw [hqF₀, PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt), PowerSeries.coeff_map] at this
    rw [hγdef]
    exact this.symm

  have hC : ∀ (φ : PowerSeries W₀ →ₐ[W₀] T) (w : W₀), φ (PowerSeries.C w) = algebraMap W₀ T w := fun φ w => by
    rw [PowerSeries.C_eq_algebraMap, AlgHom.commutes]
  have hev : ∀ φ : PowerSeries W₀ →ₐ[W₀] T, φ PowerSeries.X ∈ maximalIdeal T → ∀ r : PowerSeries W₀,
      φ r = algebraMap W₀ T (PowerSeries.constantCoeff r) + algebraMap W₀ T (PowerSeries.coeff 1 r) * φ PowerSeries.X := by
    intro φ hφX r
    have e1 := PowerSeries.eq_X_mul_shift_add_const r
    have e2 := PowerSeries.eq_X_mul_shift_add_const (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) r)
    have hc1 : PowerSeries.constantCoeff (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) r) = PowerSeries.coeff 1 r := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    rw [hc1] at e2
    conv_lhs => rw [e1, e2]
    rw [map_add, map_mul, map_add, map_mul, hC, hC, mul_add, ← mul_assoc, hsqz _ hφX, zero_mul, _root_.zero_add,
      add_comm, mul_comm]

  have hφγ : ∀ φ : PowerSeries W₀ →ₐ[W₀] T, φ PowerSeries.X ∈ maximalIdeal T → φ γ = φ PowerSeries.X := by
    intro φ hφX
    rw [hev φ hφX γ, hW₀T _ hγ₀, _root_.zero_add, show PowerSeries.coeff 1 γ = 1 + (PowerSeries.coeff 1 γ - 1) by ring,
      map_add, map_one, hW₀T _ hγ, _root_.add_zero, one_mul]

  have hclause : ∀ φ : PowerSeries W₀ →ₐ[W₀] T, φ PowerSeries.X ∈ maximalIdeal T →
      ∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r) := by
    intro φ hφX r
    rw [hev φ hφX r, map_add, map_mul, hresT₀, hresT₀, (hmemT _).mp hφX, mul_zero, _root_.add_zero]

  have hcq : ∀ (φ : PowerSeries W₀ →ₐ[W₀] T) (G' : FormalGroup T), Fu.IsBaseChange φ.toRingHom G' →
      PowerSeries.coeff q (G'.nthSeries q) = φ γ := by
    intro φ G' h
    rw [FormalGroup.IsBaseChange.nthSeries_eq_map Fu φ.toRingHom G' h q, PowerSeries.coeff_map, hγdef]
    rfl

  have hred : ∀ (φ : PowerSeries W₀ →ₐ[W₀] T), (∀ r, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) →
      ∀ (G' : FormalGroup T), Fu.IsBaseChange φ.toRingHom G' → G'.IsBaseChange resT F₀ := by
    intro φ hφ G' h
    unfold FormalGroup.IsBaseChange at h hFu ⊢
    rw [hFu, h, MvPowerSeries.map_map]
    exact congrArg (fun g : PowerSeries W₀ →+* k => MvPowerSeries.map g Fu.toPowerSeries)
      (RingHom.ext fun r => (hφ r).symm)

  set c : T := PowerSeries.coeff q (G.nthSeries q) with hcdef
  have hc : c ∈ maximalIdeal T := by
    rw [hmemT, hcdef, ← PowerSeries.coeff_map, ← FormalGroup.IsBaseChange.nthSeries_eq_map G resT F₀ hG q, hqF₀,
      PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hqlt)]
  obtain ⟨φ₀, hφ₀X⟩ := MvPowerSeries.exists_algHom_apply_X_eq (σ := Unit) (𝒪 := W₀) (maximalIdeal T)
    (fun _ => c) (fun _ => hc)
  have hφ₀X' : φ₀ PowerSeries.X = c := hφ₀X ()
  have hφ₀m : φ₀ PowerSeries.X ∈ maximalIdeal T := hφ₀X' ▸ hc

  haveI : (Fu.map φ₀.toRingHom).IsComm := FormalGroup.IsBaseChange.isComm Fu φ₀.toRingHom _ rfl
  have hbc₀ : Fu.IsBaseChange φ₀.toRingHom (Fu.map φ₀.toRingHom) := rfl
  obtain ⟨ψ, hψ⟩ := FormalGroup.exists_lawIso_of_coeff_nthSeries_eq_of_sq_maximalIdeal_eq_bot q k F₀ hF₀ T hsq
    resT hresι hkerT (Fu.map φ₀.toRingHom) G (hred φ₀ (hclause φ₀ hφ₀m) _ hbc₀) hG
    (by rw [hcq φ₀ _ hbc₀, hφγ φ₀ hφ₀m, hφ₀X'])
  refine ⟨φ₀, ⟨hclause φ₀ hφ₀m, Fu.map φ₀.toRingHom, hbc₀, ψ, hψ⟩, ?_⟩

  rintro φ' ⟨hφ'res, G'', hbc'', ψ'', hψ''⟩
  have hφ'm : φ' PowerSeries.X ∈ maximalIdeal T := by
    rw [hmemT, hφ'res, PowerSeries.constantCoeff_X, map_zero]
  have hval : φ' PowerSeries.X = c := by
    rw [← hφγ φ' hφ'm, ← hcq φ' G'' hbc'', hcdef]
    exact FormalGroup.coeff_nthSeries_eq_of_lawIso_of_sq_maximalIdeal_eq_bot q k F₀ hF₀ T hsq resT hkerT
      G'' G (hred φ' hφ'res G'' hbc'') hG ψ'' hψ''

  apply AlgHom.ext
  intro r
  rw [hev φ' hφ'm r, hev φ₀ hφ₀m r, hval, hφ₀X']

end S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_existsUnique_algHom_powerSeries_of_sq_zero_of_coeff_nthSeries (solution)
