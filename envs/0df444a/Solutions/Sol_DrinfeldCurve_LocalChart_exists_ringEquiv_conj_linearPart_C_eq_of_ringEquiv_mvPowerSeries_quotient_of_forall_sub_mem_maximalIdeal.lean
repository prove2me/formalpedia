-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8ba4c2f9-3553-5902-bbd0-6d9f68168111

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_IsLocalRing_ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal

set_option autoImplicit false

open IsLocalRing

namespace TransportLin

theorem mem_span_X_of_constantCoeff_eq_zero {O : Type*} [CommRing O] (φ : MvPowerSeries (Fin 2) O)
    (h : MvPowerSeries.constantCoeff φ = 0) :
    φ ∈ Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O), MvPowerSeries.X 1} := by
  classical
  let φ₁ : MvPowerSeries (Fin 2) O := fun m => if m 0 = 0 then φ m else 0
  have h0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) O) ∣ φ - φ₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    show φ m - φ₁ m = 0
    simp [φ₁, hm]
  have h1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) O) ∣ φ₁ := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm1
    show φ₁ m = 0
    by_cases hm0 : m 0 = 0
    · have hm : m = 0 := by
        ext i
        fin_cases i <;> simp [hm0, hm1]
      subst hm
      simp only [φ₁, if_pos hm0]
      exact (MvPowerSeries.coeff_zero_eq_constantCoeff_apply φ).trans h
    · simp [φ₁, hm0]
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  rw [Ideal.mem_span_pair]
  refine ⟨a, b, ?_⟩
  rw [mul_comm a, mul_comm b, ← ha, ← hb]
  ring

end TransportLin

open TransportLin in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : maximalIdeal W = Ideal.span {ϖ})
    (f u v : MvPowerSeries (Fin 2) W) (hu : IsUnit u) (hv : IsUnit v)
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hx₀ : e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0)) (hx₁ : e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1))
    (θ₀ : R ≃+* R) (hres : ∀ r : R, θ₀ r - r ∈ maximalIdeal R)
    (hfix : θ₀ (e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ))) = e.symm (Ideal.Quotient.mk _ (MvPowerSeries.C ϖ)))
    (c : R) (g : Matrix (Fin 2) (Fin 2) ℤ)
    (hlin₀ : θ₀ x₀ - c * (((g 0 0 : ℤ) : R) * x₀ + ((g 1 0 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)
    (hlin₁ : θ₀ x₁ - c * (((g 0 1 : ℤ) : R) * x₀ + ((g 1 1 : ℤ) : R) * x₁) ∈ (maximalIdeal R) ^ 2)
    (hc : c ^ (q + 1) - 1 ∈ maximalIdeal R)
    (P P' P'' : Prop) (hP : P → c - 1 ∈ maximalIdeal R) (hP' : P' → P'' → c - 1 ∉ maximalIdeal R) :
    let S := (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    let mkS : MvPowerSeries (Fin 2) W →+* S := Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C ϖ * v - f * u})
    ∃ (θ : S ≃+* S) (c' : W) (M : Matrix (Fin 2) (Fin 2) W),
      (∀ r : R, θ (e r) = e (θ₀ r)) ∧
      (∀ w : W, θ (mkS (MvPowerSeries.C w)) = mkS (MvPowerSeries.C w)) ∧
      (∀ jj : Fin 2, θ (mkS (MvPowerSeries.X jj)) -
          mkS (∑ ii : Fin 2, MvPowerSeries.C (M ii jj) * MvPowerSeries.X ii) ∈
        (Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}) ^ 2) ∧
      (c' ^ (q + 1) - 1 ∈ maximalIdeal W) ∧
      (∀ ii jj : Fin 2, M ii jj - c' * ((g ii jj : ℤ) : W) ∈ maximalIdeal W) ∧
      (P → c' - 1 ∈ maximalIdeal W) ∧
      (P' → P'' → c' - 1 ∉ maximalIdeal W) := by
  intro S mkS
  classical

  let 𝔛 : Ideal (MvPowerSeries (Fin 2) W) := Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}
  let 𝔫 : Ideal S := Ideal.span {mkS (MvPowerSeries.X 0), mkS (MvPowerSeries.X 1)}
  let κ : W →+* R := e.symm.toRingHom.comp (mkS.comp MvPowerSeries.C)
  have hκ : ∀ w : W, κ w = e.symm (mkS (MvPowerSeries.C w)) := fun w => rfl
  have heκ : ∀ w : W, e (κ w) = mkS (MvPowerSeries.C w) := fun w => by
    rw [hκ, RingEquiv.apply_symm_apply]

  have h𝔫 : 𝔫 = (maximalIdeal R).map (e : R →+* S) := by
    rw [hmax, Ideal.map_span, Set.image_pair]
    show 𝔫 = Ideal.span {e x₀, e x₁}
    rw [hx₀, hx₁]
  have hmem𝔫 : ∀ (k : ℕ) (r : R), e r ∈ 𝔫 ^ k ↔ r ∈ maximalIdeal R ^ k := by
    intro k r
    rw [h𝔫, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    simp
  have hmem𝔫1 : ∀ r : R, e r ∈ 𝔫 ↔ r ∈ maximalIdeal R := by
    intro r
    rw [h𝔫, Ideal.map_comap_of_equiv, Ideal.mem_comap]
    simp

  have h𝔛𝔫 : 𝔛.map mkS = 𝔫 := by
    show Ideal.map mkS (Ideal.span _) = _
    rw [Ideal.map_span, Set.image_pair]
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) ∈ 𝔛 := Ideal.subset_span (by simp)
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) ∈ 𝔛 := Ideal.subset_span (by simp)
  have hf𝔛 : f ∈ 𝔛 := by
    have hdf : DrinfeldCurve.LocalChart.drinfeldForm q W ∈ 𝔛 := by
      show MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ q - MvPowerSeries.X 0 ^ q * MvPowerSeries.X 1 ∈ 𝔛
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hX0) (Ideal.mul_mem_left _ _ hX1)
    have h1 : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ 𝔛 :=
      Ideal.pow_le_self (by omega) hf
    have := Ideal.add_mem _ h1 hdf
    simpa using this
  have hY0 : mkS (MvPowerSeries.X 0) ∈ 𝔫 := Ideal.subset_span (by simp)
  have hY1 : mkS (MvPowerSeries.X 1) ∈ 𝔫 := Ideal.subset_span (by simp)
  have hf𝔫 : mkS f ∈ 𝔫 := h𝔛𝔫 ▸ Ideal.mem_map_of_mem mkS hf𝔛
  have hvS : IsUnit (mkS v) := hv.map mkS
  have hϖ𝔫 : mkS (MvPowerSeries.C ϖ) ∈ 𝔫 := by
    have hrel : mkS (MvPowerSeries.C ϖ) * mkS v = mkS f * mkS u := by
      rw [← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have : mkS (MvPowerSeries.C ϖ) = mkS f * mkS u * ↑(hvS.unit⁻¹) := by
      rw [← hrel, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hf𝔫)

  have hκϖ : κ ϖ ∈ maximalIdeal R := by
    rw [← hmem𝔫1, heκ]; exact hϖ𝔫
  have hκm : ∀ w : W, κ w ∈ maximalIdeal R ↔ w ∈ maximalIdeal W := by
    intro w
    constructor
    · intro hw
      by_contra hw'
      have hwu : IsUnit w := by
        simpa [mem_maximalIdeal, mem_nonunits_iff] using hw'
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hw)) (hwu.map κ)
    · intro hw
      rw [hϖ, Ideal.mem_span_singleton'] at hw
      obtain ⟨t, rfl⟩ := hw
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ hκϖ
  haveI : IsLocalHom κ := ⟨fun a ha => by
    by_contra hna
    have : a ∈ maximalIdeal W := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hna
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp ((hκm a).mpr this))) ha⟩

  have hW : (θ₀ : R →+* R).comp κ = κ :=
    IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span
      W ϖ hϖ R κ (θ₀ : R →+* R) (fun r => by simpa using hres r) (by simpa [hκ] using hfix)
  have hWlin : ∀ w : W, θ₀ (κ w) = κ w := fun w => by
    have := RingHom.congr_fun hW w
    simpa using this

  let θ : S ≃+* S := (e.symm.trans θ₀).trans e
  have hθ : ∀ s : S, θ s = e (θ₀ (e.symm s)) := fun s => rfl

  obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {MvPowerSeries.C ϖ * v - f * u}) (e c)
  let c' : W := MvPowerSeries.constantCoeff γ
  have hcc' : e c - mkS (MvPowerSeries.C c') ∈ 𝔫 := by
    rw [← hγ, ← h𝔛𝔫]
    show mkS γ - mkS (MvPowerSeries.C c') ∈ Ideal.map mkS 𝔛
    rw [← map_sub]
    refine Ideal.mem_map_of_mem mkS (mem_span_X_of_constantCoeff_eq_zero _ ?_)
    simp [c']
  have hcκ : c - κ c' ∈ maximalIdeal R := by
    rw [← hmem𝔫1, map_sub, heκ]; exact hcc'
  have hquot : Ideal.Quotient.mk (maximalIdeal R) c = Ideal.Quotient.mk (maximalIdeal R) (κ c') :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hcκ

  let M : Matrix (Fin 2) (Fin 2) W := fun ii jj => c' * ((g ii jj : ℤ) : W)
  refine ⟨θ, c', M, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro r
    rw [hθ, RingEquiv.symm_apply_apply]
  ·
    intro w
    rw [hθ, ← hκ, hWlin, heκ]
  ·
    have hex₀ : e.symm (mkS (MvPowerSeries.X 0)) = x₀ := by
      rw [← hx₀]; exact e.symm_apply_apply x₀
    have hex₁ : e.symm (mkS (MvPowerSeries.X 1)) = x₁ := by
      rw [← hx₁]; exact e.symm_apply_apply x₁
    have key : ∀ (y : R) (a b : ℤ), θ₀ y - c * ((a : R) * x₀ + (b : R) * x₁) ∈ maximalIdeal R ^ 2 →
        e (θ₀ y) - mkS (MvPowerSeries.C (c' * (a : W)) * MvPowerSeries.X 0 +
          MvPowerSeries.C (c' * (b : W)) * MvPowerSeries.X 1) ∈ 𝔫 ^ 2 := by
      intro y a b hy
      rw [← hmem𝔫 2] at hy
      have hy' : e (θ₀ y) - e c * ((a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1)) ∈ 𝔫 ^ 2 := by
        simpa [map_sub, map_mul, map_add, map_intCast, hx₀, hx₁] using hy
      have hL : (a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1) ∈ 𝔫 :=
        Ideal.add_mem _ (Ideal.mul_mem_left _ _ hY0) (Ideal.mul_mem_left _ _ hY1)
      have hrw : mkS (MvPowerSeries.C (c' * (a : W)) * MvPowerSeries.X 0 +
          MvPowerSeries.C (c' * (b : W)) * MvPowerSeries.X 1) =
          mkS (MvPowerSeries.C c') * ((a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1)) := by
        simp only [map_add, map_mul, map_intCast]
        ring
      rw [hrw]
      have : e (θ₀ y) - mkS (MvPowerSeries.C c') * ((a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1)) =
          (e (θ₀ y) - e c * ((a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1))) +
          (e c - mkS (MvPowerSeries.C c')) * ((a : S) * mkS (MvPowerSeries.X 0) + (b : S) * mkS (MvPowerSeries.X 1)) := by
        ring
      rw [this, pow_two]
      exact Ideal.add_mem _ (pow_two 𝔫 ▸ hy') (Ideal.mul_mem_mul hcc' hL)
    intro jj
    fin_cases jj
    · have := key x₀ (g 0 0) (g 1 0) hlin₀
      simpa [hθ, hex₀, M, Fin.sum_univ_two] using this
    · have := key x₁ (g 0 1) (g 1 1) hlin₁
      simpa [hθ, hex₁, M, Fin.sum_univ_two] using this
  ·
    rw [← hκm, ← Ideal.Quotient.eq_zero_iff_mem]
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hc
    simpa [map_sub, map_pow, hquot] using hc
  ·
    intro ii jj
    simp [M]
  · intro hp
    have h1 := hP hp
    rw [← hκm, map_sub, map_one]
    have : κ c' - 1 = (c - 1) - (c - κ c') := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 hcκ
  · intro hp' hp'' hmem
    apply hP' hp' hp''
    rw [← hκm, map_sub, map_one] at hmem
    have : c - 1 = (c - κ c') + (κ c' - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ hcκ hmem

end S_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_ringEquiv_conj_linearPart_C_eq_of_ringEquiv_mvPowerSeries_quotient_of_forall_sub_mem_maximalIdeal (solution)
