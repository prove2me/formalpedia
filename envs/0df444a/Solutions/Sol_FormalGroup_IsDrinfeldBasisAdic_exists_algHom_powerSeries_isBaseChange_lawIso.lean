-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.exists_algHom_powerSeries_isBaseChange_lawIso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9de2ac0a-1244-55da-9e61-eda44e45215d

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsBaseChange_isComm
import Theorems.Thm_FormalGroup_LawHom_exists_isBaseChange_series_eq_map
import Theorems.Thm_FormalGroup_LawHom_series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_FormalGroup_exists_lawIso_of_forall_isBaseChange_mk_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_isBaseChange_lawIso
p2m_attr_erase "instance" "MvFormalGroup.instIsCommOfFormalGroup MvFormalGroup.instIsCommAddMv MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing"
p2m_attr_erase "simp" "MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

open FormalGroup IsLocalRing

theorem solution
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q]
    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    (F₀ : FormalGroup k) [F₀.IsComm] (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra W₀ R] [IsAdicComplete (maximalIdeal R) R] [IsNoetherianRing R]
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)
    (F : FormalGroup R) [F.IsComm] (hF : F.IsBaseChange resR F₀)
    (Fu : FormalGroup (PowerSeries W₀)) [Fu.IsComm]
    (hFu : Fu.IsBaseChange (res₀.comp (PowerSeries.constantCoeff : PowerSeries W₀ →+* W₀)) F₀)
    (hLT : (∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
          (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
          (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
          ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
            ∃! φ : PowerSeries W₀ →ₐ[W₀] T,
              (∀ r : PowerSeries W₀, resT (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧
              ∃ (G' : FormalGroup T) (_ : Fu.IsBaseChange φ.toRingHom G') (ψ : FormalGroup.LawIso G' G),
                ∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0)) :
    ∃ (φ : PowerSeries W₀ →ₐ[W₀] R),
      (∀ r : PowerSeries W₀, resR (φ r) = res₀ (PowerSeries.constantCoeff r)) ∧ φ PowerSeries.X ∈ maximalIdeal R ∧
      ∃ (F' : FormalGroup R) (_ : Fu.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' F),
        ∀ n : ℕ, resR (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0 := by
  classical

  have hq0 : (q : W₀) ∈ RingHom.ker res₀ := by
    rw [hker₀, hW₀]; exact Ideal.mem_span_singleton_self _
  have hqR : (q : R) ∈ maximalIdeal R := by
    rw [← hkerR, RingHom.mem_ker, ← map_natCast (algebraMap W₀ R), hresR₀]
    exact hq0
  have hIle : ∀ n : ℕ, maximalIdeal R ^ (n + 1) ≤ maximalIdeal R := fun n =>
    Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hIker : ∀ n : ℕ, ∀ r ∈ maximalIdeal R ^ (n + 1), resR r = 0 := fun n r hr => by
    rw [← RingHom.mem_ker, hkerR]; exact hIle n hr
  have hIne : ∀ n : ℕ, maximalIdeal R ^ (n + 1) ≠ ⊤ := fun n h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIle n))

  let resT : ∀ n : ℕ, R ⧸ maximalIdeal R ^ (n + 1) →+* k := fun n =>
    Ideal.Quotient.lift (maximalIdeal R ^ (n + 1)) resR (hIker n)
  have resT_mk : ∀ n r, resT n (Ideal.Quotient.mk _ r) = resR r := fun n r => Ideal.Quotient.lift_mk _ _ _
  have resT_surj : ∀ n, Function.Surjective (resT n) := fun n a => by
    obtain ⟨r, rfl⟩ := hresR a; exact ⟨Ideal.Quotient.mk _ r, resT_mk n r⟩
  haveI instNontriv : ∀ n : ℕ, Nontrivial (R ⧸ maximalIdeal R ^ (n + 1)) := fun n =>
    Ideal.Quotient.nontrivial_iff.mpr (hIne n)
  haveI instLocal : ∀ n : ℕ, IsLocalRing (R ⧸ maximalIdeal R ^ (n + 1)) := fun n =>
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hmaxT : ∀ n : ℕ, maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) =
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) := fun n => by
    haveI : ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIle n)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hkerT : ∀ n : ℕ, RingHom.ker (resT n) = maximalIdeal (R ⧸ maximalIdeal R ^ (n + 1)) := fun n =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (resT n) (resT_surj n))
  haveI instArt : ∀ n : ℕ, IsArtinianRing (R ⧸ maximalIdeal R ^ (n + 1)) := fun n => by
    rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
    refine ⟨n + 1, ?_⟩
    rw [hmaxT, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  have hresT₀ : ∀ (n : ℕ) (w : W₀), resT n (algebraMap W₀ (R ⧸ maximalIdeal R ^ (n + 1)) w) = res₀ w :=
    fun n w => by
      show resT n (Ideal.Quotient.mk _ (algebraMap W₀ R w)) = res₀ w
      rw [resT_mk, hresR₀]

  haveI instComm : ∀ n : ℕ, (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))).IsComm := fun n =>
    FormalGroup.IsBaseChange.isComm F _ _ rfl
  have hGn : ∀ n : ℕ, (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))).IsBaseChange (resT n) F₀ := by
    intro n
    unfold FormalGroup.IsBaseChange at hF ⊢
    rw [hF, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map]
    exact congrArg (fun g : R →+* k => MvPowerSeries.map g F.toPowerSeries)
      (RingHom.ext fun r => (resT_mk n r).symm)

  have LT := fun n : ℕ => hLT (R ⧸ maximalIdeal R ^ (n + 1)) (resT n) (resT_surj n) (hkerT n) (hresT₀ n)
    (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) (hGn n)
  let φn : ∀ n : ℕ, PowerSeries W₀ →ₐ[W₀] (R ⧸ maximalIdeal R ^ (n + 1)) := fun n => (LT n).exists.choose
  have φn_spec := fun n : ℕ => (LT n).exists.choose_spec
  have φn_uniq : ∀ (n : ℕ) (φ' : PowerSeries W₀ →ₐ[W₀] (R ⧸ maximalIdeal R ^ (n + 1))),
      ((∀ r, resT n (φ' r) = res₀ (PowerSeries.constantCoeff r)) ∧
        ∃ (G' : FormalGroup (R ⧸ maximalIdeal R ^ (n + 1))) (_ : Fu.IsBaseChange φ'.toRingHom G')
          (ψ : FormalGroup.LawIso G' (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))))),
          ∀ m : ℕ, resT n (PowerSeries.coeff m ψ.series) = if m = 1 then 1 else 0) → φ' = φn n :=
    fun n φ' h => (LT n).unique h (φn_spec n)

  have hle : ∀ n : ℕ, maximalIdeal R ^ (n + 1 + 1) ≤ maximalIdeal R ^ (n + 1) := fun n =>
    Ideal.pow_le_pow_right (Nat.le_succ _)
  have fac_mk : ∀ (n : ℕ) (r : R), Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))
      (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := fun n r => Ideal.Quotient.factor_mk _ _
  have resT_fac : ∀ (n : ℕ) (x : R ⧸ maximalIdeal R ^ (n + 1 + 1)),
      resT n (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)) x) = resT (n + 1) x := by
    intro n x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [fac_mk, resT_mk, resT_mk]
  have facₐ_apply : ∀ (n : ℕ) (x : R ⧸ maximalIdeal R ^ (n + 1 + 1)),
      Ideal.Quotient.factorₐ W₀ (hle n) x = Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)) x :=
    fun n x => rfl
  have hGdown : ∀ n : ℕ, (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1 + 1)))).IsBaseChange
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)))
      (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) := by
    intro n
    unfold FormalGroup.IsBaseChange
    rw [FormalGroup.map_toPowerSeries, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map]
    exact congrArg (fun g : R →+* R ⧸ maximalIdeal R ^ (n + 1) => MvPowerSeries.map g F.toPowerSeries)
      (RingHom.ext fun r => (fac_mk n r).symm)
  have compat : ∀ n : ℕ, (Ideal.Quotient.factorₐ W₀ (hle n)).comp (φn (n + 1)) = φn n := by
    intro n
    apply φn_uniq
    obtain ⟨hres, G', hG', ψ, hψ⟩ := φn_spec (n + 1)
    refine ⟨fun r => ?_, ?_⟩
    · rw [AlgHom.comp_apply, facₐ_apply, resT_fac]; exact hres r
    · obtain ⟨ψ', hψ'⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map
        (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))) ψ.toLawHom
        (G'.map (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))))
        (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) rfl (hGdown n)
      refine ⟨G'.map (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))), ?_,
        ⟨ψ', ?_⟩, fun m => ?_⟩
      · unfold FormalGroup.IsBaseChange at hG' ⊢
        rw [FormalGroup.map_toPowerSeries, hG', MvPowerSeries.map_map]
        exact congrArg (fun g : PowerSeries W₀ →+* R ⧸ maximalIdeal R ^ (n + 1) =>
          MvPowerSeries.map g Fu.toPowerSeries) (RingHom.ext fun r => rfl)
      · rw [hψ', PowerSeries.coeff_map]; exact (ψ.isUnit_coeff_one).map _
      · show resT n (PowerSeries.coeff m ψ'.series) = _
        rw [hψ', PowerSeries.coeff_map, resT_fac]; exact hψ m

  have hsm : StrictMono (fun n : ℕ => n + 1) := fun a b h => Nat.succ_lt_succ h
  have hf : ∀ {m : ℕ}, (Ideal.Quotient.factorPow (maximalIdeal R) (hsm.monotone m.le_succ)).comp
      (φn (m + 1)).toRingHom = (φn m).toRingHom := by
    intro m
    refine RingHom.ext fun r => ?_
    show Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (m + 1)) (φn (m + 1) r) = φn m r
    rw [← facₐ_apply, ← AlgHom.comp_apply, compat]
  let φ : PowerSeries W₀ →+* R :=
    IsAdicComplete.StrictMono.liftRingHom (maximalIdeal R) hsm (fun n => (φn n).toRingHom) hf
  have φ_mk : ∀ (n : ℕ) (r : PowerSeries W₀), Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)) (φ r) = φn n r :=
    fun n r => IsAdicComplete.StrictMono.mk_liftRingHom (maximalIdeal R) hsm _ hf r
  have φ_alg : ∀ w : W₀, φ (algebraMap W₀ (PowerSeries W₀) w) = algebraMap W₀ R w := by
    intro w
    refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n =>
      rw [← Ideal.Quotient.eq, φ_mk, AlgHom.commutes]
      rfl
  let φA : PowerSeries W₀ →ₐ[W₀] R := { toRingHom := φ, commutes' := φ_alg }
  have clause1 : ∀ r, resR (φ r) = res₀ (PowerSeries.constantCoeff r) := fun r => by
    rw [← resT_mk 0, φ_mk]; exact (φn_spec 0).1 r
  have clause2 : φ PowerSeries.X ∈ maximalIdeal R := by
    rw [← hkerR, RingHom.mem_ker, clause1, PowerSeries.constantCoeff_X, map_zero]

  choose G' hG' ψ hψ using fun n => (φn_spec n).2
  have hG'red : ∀ n : ℕ, (G' n).IsBaseChange (resT n) F₀ := by
    intro n
    have e := hG' n
    unfold FormalGroup.IsBaseChange at e hFu ⊢
    rw [hFu, e, MvPowerSeries.map_map]
    exact congrArg (fun g : PowerSeries W₀ →+* k => MvPowerSeries.map g Fu.toPowerSeries)
      (RingHom.ext fun r => ((φn_spec n).1 r).symm)
  have hG'down : ∀ n : ℕ, (G' (n + 1)).IsBaseChange
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))) (G' n) := by
    intro n
    have e := hG' n
    have e' := hG' (n + 1)
    unfold FormalGroup.IsBaseChange at e e' ⊢
    rw [e, e', MvPowerSeries.map_map]
    exact congrArg (fun g : PowerSeries W₀ →+* R ⧸ maximalIdeal R ^ (n + 1) =>
      MvPowerSeries.map g Fu.toPowerSeries) (RingHom.ext fun r => by
        show (φn n).toRingHom r = Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)) ((φn (n + 1)).toRingHom r)
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          ← facₐ_apply, ← AlgHom.comp_apply, compat])
  have hψcompat : ∀ n : ℕ, PowerSeries.map (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1)))
      (ψ (n + 1)).series = (ψ n).series := by
    intro n
    obtain ⟨ψ', hψ'⟩ := FormalGroup.LawHom.exists_isBaseChange_series_eq_map
      (Ideal.Quotient.factorPow (maximalIdeal R) (Nat.le_succ (n + 1))) (ψ (n + 1)).toLawHom
      (G' n) (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) (hG'down n) (hGdown n)
    rw [← hψ']
    symm
    refine FormalGroup.LawHom.series_eq_of_map_series_eq_of_surjective_of_ker_pow_eq_bot q (resT n)
      (resT_surj n) (n + 1) ?_ ?_
      F₀ hF₀ (G' n) (F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) (hG'red n) (hGn n)
      (ψ n).toLawHom ψ' ?_
    · rw [hkerT, hmaxT, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    · rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hqR _
    · ext m
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, hψ', PowerSeries.coeff_map, resT_fac]
      show resT n (PowerSeries.coeff m (ψ n).series) = resT (n + 1) (PowerSeries.coeff m (ψ (n + 1)).series)
      rw [hψ n m, hψ (n + 1) m]

  have hF'q : ∀ n : ℕ, (Fu.map φ).IsBaseChange (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (G' n) := by
    intro n
    have e := hG' n
    unfold FormalGroup.IsBaseChange at e ⊢
    rw [e, FormalGroup.map_toPowerSeries, MvPowerSeries.map_map]
    exact congrArg (fun g : PowerSeries W₀ →+* R ⧸ maximalIdeal R ^ (n + 1) =>
      MvPowerSeries.map g Fu.toPowerSeries) (RingHom.ext fun r => by
        show (φn n).toRingHom r = Ideal.Quotient.mk _ (φ r)
        rw [φ_mk]; rfl)
  obtain ⟨Ψ, hΨ⟩ := FormalGroup.exists_lawIso_of_forall_isBaseChange_mk_pow (Fu.map φ) F G'
    (fun n => F.map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) hF'q (fun n => rfl) ψ hψcompat
  refine ⟨φA, clause1, clause2, Fu.map φ, rfl, Ψ, fun m => ?_⟩
  rw [← resT_mk 0, ← PowerSeries.coeff_map, hΨ 0]
  exact hψ 0 m

end S_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_isBaseChange_lawIso
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_exists_algHom_powerSeries_isBaseChange_lawIso (solution)
