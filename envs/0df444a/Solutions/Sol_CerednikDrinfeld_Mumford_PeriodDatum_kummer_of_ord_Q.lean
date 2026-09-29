-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodDatum.kummer_of_ord_Q
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c9d2a473-8149-51c1-b1fb-d8f61df15513

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_CerednikDrinfeld_ToricUniformization
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (χ : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) → (↥(ribbonKernel D) →ₗ[ℤ] ZMod p))
    (hχ : ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
      Additive.toMul (((v : ↥P.U) : P.TorusPoints) z) = ζ ^ (χ v z).val)
    (s : L →+* L) (hsK : ∀ k : K, s (algebraMap K L k) = algebraMap K L k) (hsζ : s ζ = ζ)
    (ϖ : Kˣ) (hϖ : ord (Additive.ofMul ϖ) = 1)
    (hensel : ∀ a : Kˣ, ord (Additive.ofMul a) = 0 → ∃ c : Kˣ, c ^ p = a)
    (τ : ZMod p) (hτ : ∀ b : L, b ^ p = algebraMap K L ϖ → s b = (ζ : L) ^ τ.val * b)
    (u : ↥P.U) (x : ↥(ribbonKernel D)) (hu : (p : ℤ) • (u : P.TorusPoints) = P.QL x) :
    ∃ v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)),
      (∀ z : ↥(ribbonKernel D),
        Additive.ofMul (Units.map (s : L →* L) (Additive.toMul ((u : P.TorusPoints) z))) =
          (u : P.TorusPoints) z + ((v : ↥P.U) : P.TorusPoints) z) ∧
      χ v = τ • ribbonGramModP p D x := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  let ι : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  let sU : Lˣ →* Lˣ := Units.map (s : L →* L)
  have hιval : ∀ k : Kˣ, ((ι k : Lˣ) : L) = algebraMap K L k := fun k => rfl
  have hsUval : ∀ w : Lˣ, ((sU w : Lˣ) : L) = s w := fun w => rfl
  have hsι : ∀ k : Kˣ, sU (ι k) = ι k := fun k => Units.ext (by rw [hsUval, hιval, hsK])
  have hsζ' : sU ζ = ζ := Units.ext (by rw [hsUval, hsζ])

  have hup : ∀ z : ↥(ribbonKernel D),
      (Additive.toMul ((u : P.TorusPoints) z)) ^ (p : ℤ) = ι (Additive.toMul (P.Q x z)) := by
    intro z
    have h1 := LinearMap.congr_fun hu z
    rw [LinearMap.smul_apply, PeriodDatum.QL_apply] at h1
    have h2 := congrArg Additive.toMul h1
    rw [toMul_zsmul] at h2
    rw [h2]
    rfl

  have key : ∀ z : ↥(ribbonKernel D),
      sU (Additive.toMul ((u : P.TorusPoints) z)) =
        ζ ^ ((τ.val : ℤ) * ribbonGram D x z) * Additive.toMul ((u : P.TorusPoints) z) := by
    intro z

    obtain ⟨uz, huz⟩ : ∃ uz : Lˣ, uz = Additive.toMul ((u : P.TorusPoints) z) := ⟨_, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : Kˣ, a = Additive.toMul (P.Q x z) := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : ℤ, g = ribbonGram D x z := ⟨_, rfl⟩
    rw [← huz, ← hg]
    have hupz : uz ^ (p : ℤ) = ι a := by rw [huz, ha]; exact hup z
    have horda : ord (Additive.ofMul a) = g := by rw [ha, ofMul_toMul, hg]; exact P.ord_Q x z

    have hordw : ord (Additive.ofMul (a * ϖ ^ (-g))) = 0 := by
      rw [ofMul_mul, ofMul_zpow, map_add, map_zsmul, horda, hϖ, smul_eq_mul, mul_one, add_neg_cancel]
    obtain ⟨c, hc⟩ := hensel (a * ϖ ^ (-g)) hordw
    have ha' : a = ϖ ^ g * c ^ p := by
      rw [hc, mul_left_comm, zpow_neg, mul_inv_cancel, mul_one]

    obtain ⟨y, hy⟩ : ∃ y : Lˣ, y = uz * (ι c)⁻¹ := ⟨_, rfl⟩
    have huzy : uz = y * ι c := by rw [hy, inv_mul_cancel_right]
    have hyp : y ^ (p : ℤ) = ι ϖ ^ g := by
      rw [hy, mul_zpow, inv_zpow, hupz, ha', map_mul, map_zpow, map_pow, zpow_natCast, mul_inv_cancel_right]

    have hsy : sU y = ζ ^ ((τ.val : ℤ) * g) * y := by
      by_cases hdvd : (p : ℤ) ∣ g
      · obtain ⟨q, hq⟩ := hdvd
        obtain ⟨ξ, hξ⟩ : ∃ ξ : Lˣ, ξ = y * (ι ϖ ^ q)⁻¹ := ⟨_, rfl⟩
        have hξp : ξ ^ p = 1 := by
          rw [← zpow_natCast, hξ, mul_zpow, inv_zpow, hyp, hq, ← zpow_mul, mul_comm q (p : ℤ),
            mul_inv_cancel]
        obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p ξ).mpr hξp)
        have hy' : y = ζ ^ i * ι ϖ ^ q := by rw [hi, hξ, inv_mul_cancel_right]
        have h1 : sU y = y := by rw [hy', map_mul, map_pow, map_zpow, hsζ', hsι]
        have h2 : ζ ^ ((τ.val : ℤ) * g) = 1 := by
          rw [hζ.zpow_eq_one_iff_dvd, hq]
          exact ⟨(τ.val : ℤ) * q, by ring⟩
        rw [h1, h2, one_mul]
      · have hcop : IsCoprime (p : ℤ) g :=
          (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hdvd
        obtain ⟨β, α, hαβ⟩ := hcop
        obtain ⟨ρ, hρ⟩ : ∃ ρ : Lˣ, ρ = y ^ α * ι ϖ ^ β := ⟨_, rfl⟩
        have hρp' : ρ ^ (p : ℤ) = ι ϖ := by
          rw [hρ, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm α (p : ℤ), zpow_mul, hyp, ← zpow_mul,
            ← zpow_add]
          have h1 : g * α + β * (p : ℤ) = 1 := by linarith [hαβ]
          rw [h1, zpow_one]
        have hρp : (ρ : L) ^ p = algebraMap K L ϖ := by
          have h1 := congrArg (fun w : Lˣ => (w : L)) hρp'
          simp only [zpow_natCast, Units.val_pow_eq_pow_val] at h1
          rw [h1]
          exact hιval ϖ
        have hsρ : sU ρ = ζ ^ τ.val * ρ := by
          apply Units.ext
          rw [hsUval, Units.val_mul, Units.val_pow_eq_pow_val]
          exact hτ ρ hρp
        have hyρ : y = ρ ^ g := by
          calc y = y ^ (β * (p : ℤ) + α * g) := by rw [hαβ, zpow_one]
            _ = (y ^ (p : ℤ)) ^ β * (y ^ α) ^ g := by
                rw [zpow_add, mul_comm β (p : ℤ), zpow_mul, zpow_mul]
            _ = (ι ϖ ^ g) ^ β * (y ^ α) ^ g := by rw [hyp]
            _ = ρ ^ g := by
                rw [hρ, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm g β, mul_comm]
        rw [hyρ, map_zpow, hsρ, mul_zpow, ← zpow_natCast, ← zpow_mul]

    rw [huzy, map_mul, hsι, hsy, mul_assoc]

  let vTP : P.TorusPoints :=
    (MonoidHom.toAdditive sU).toIntLinearMap ∘ₗ (u : P.TorusPoints) - (u : P.TorusPoints)
  have hvTP : ∀ z : ↥(ribbonKernel D),
      vTP z = Additive.ofMul (ζ ^ ((τ.val : ℤ) * ribbonGram D x z)) := by
    intro z
    show Additive.ofMul (sU (Additive.toMul ((u : P.TorusPoints) z))) - (u : P.TorusPoints) z = _
    rw [key z, ofMul_mul, ofMul_toMul, add_sub_cancel_right]
  have hpv : (p : ℤ) • vTP = 0 := by
    refine LinearMap.ext fun z => ?_
    rw [LinearMap.smul_apply, hvTP, LinearMap.zero_apply, ← ofMul_zpow, ← zpow_mul, ofMul_eq_zero,
      hζ.zpow_eq_one_iff_dvd]
    exact ⟨(τ.val : ℤ) * ribbonGram D x z, by ring⟩
  have hvU : vTP ∈ P.U := by
    simp only [PeriodDatum.U, Submodule.mem_comap]
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp.ne_zero)⟩, ?_⟩
    show (p : ℤ) • P.periodLattice.mkQ vTP = 0
    rw [← map_zsmul, hpv, map_zero]
  have hvT : (⟨vTP, hvU⟩ : ↥P.U) ∈ Submodule.torsionBy ℤ ↥P.U (p : ℤ) := by
    rw [Submodule.mem_torsionBy_iff]
    apply Subtype.ext
    exact hpv
  refine ⟨⟨⟨vTP, hvU⟩, hvT⟩, fun z => ?_, ?_⟩
  · show _ = (u : P.TorusPoints) z + vTP z
    rw [hvTP z]
    show Additive.ofMul (sU (Additive.toMul ((u : P.TorusPoints) z))) = _
    rw [key z, ofMul_mul, ofMul_toMul, add_comm]
  · refine LinearMap.ext fun z => ?_
    have h1 := hχ ⟨⟨vTP, hvU⟩, hvT⟩ z
    have h2 : Additive.toMul (vTP z) = ζ ^ ((τ.val : ℤ) * ribbonGram D x z) := by
      rw [hvTP, toMul_ofMul]
    have h3 : ζ ^ (((χ ⟨⟨vTP, hvU⟩, hvT⟩ z).val : ℤ)) = ζ ^ ((τ.val : ℤ) * ribbonGram D x z) := by
      rw [zpow_natCast, ← h2]
      exact h1.symm
    have h4 : (p : ℤ) ∣ ((τ.val : ℤ) * ribbonGram D x z) - ((χ ⟨⟨vTP, hvU⟩, hvT⟩ z).val : ℤ) := by
      rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub, ← h3, mul_inv_cancel]
    have h5 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ p).mpr h4
    rw [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] at h5
    rw [LinearMap.smul_apply, ribbonGramModP_apply, smul_eq_mul]
    exact h5

end S_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_kummer_of_ord_Q (solution)
