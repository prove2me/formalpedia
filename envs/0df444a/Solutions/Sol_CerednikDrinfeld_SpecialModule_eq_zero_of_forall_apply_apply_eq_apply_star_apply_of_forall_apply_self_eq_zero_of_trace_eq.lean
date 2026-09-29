-- Prove2me | solution 1 for CerednikDrinfeld.SpecialModule.eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0b9dfdf1-d3bd-54a0-a5ff-fa0a1880a58a

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialModule_eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
p2m_attr_erase "instance" "CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction"
p2m_attr_erase "simp" "QuaternionAlgebra.ClassSet.map_mk QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace RKcore

variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]

theorem bf_eq_zero_of_span (v₁ v₂ : W) (hspan : ∀ v : W, ∃ s t : k, v = s • v₁ + t • v₂)
    (bf : W →ₗ[k] W →ₗ[k] k) (h11 : bf v₁ v₁ = 0) (h12 : bf v₁ v₂ = 0) (h21 : bf v₂ v₁ = 0) (h22 : bf v₂ v₂ = 0) :
    bf = 0 := by
  ext v w
  obtain ⟨s, t, rfl⟩ := hspan v
  obtain ⟨s', t', rfl⟩ := hspan w
  simp [h11, h12, h21, h22]

theorem eigenbasis_of_quadratic [FiniteDimensional k W] (h2 : Module.finrank k W = 2)
    (Ω : W →ₗ[k] W) (α α' : k) (hne : α ≠ α')
    (hΩ : (Ω - α • LinearMap.id) ∘ₗ (Ω - α' • LinearMap.id) = 0)
    (htr : LinearMap.trace k W Ω = α + α') :
    ∃ v₁ v₂ : W, (∀ v : W, ∃ s t : k, v = s • v₁ + t • v₂) ∧ v₁ ≠ 0 ∧ v₂ ≠ 0 ∧
      Ω v₁ = α • v₁ ∧ Ω v₂ = α' • v₂ := by
  classical
  have hΩv : ∀ v, Ω (Ω v - α' • v) = α • (Ω v - α' • v) := fun v => by
    have h0 := congrArg (fun f : W →ₗ[k] W => f v) hΩ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul, LinearMap.zero_apply] at h0
    rw [map_sub, map_smul, ← sub_eq_zero, ← h0]
    module

  have hΩv' : ∀ v, Ω (Ω v - α • v) = α' • (Ω v - α • v) := fun v => by
    have h := hΩv v
    rw [map_sub, map_smul] at h ⊢
    rw [smul_sub, smul_smul] at h ⊢
    have : Ω (Ω v) = α • Ω v + α' • Ω v - (α * α') • v := by
      rw [sub_eq_iff_eq_add] at h; rw [h]; module
    rw [this]; module

  have hG : ∃ u, Ω u - α' • u ≠ 0 := by
    by_contra h; push Not at h
    have hΩeq : Ω = α' • LinearMap.id := LinearMap.ext fun v => by simpa [sub_eq_zero] using h v
    rw [hΩeq, map_smul, LinearMap.trace_id, h2, smul_eq_mul] at htr
    apply hne; linear_combination (-1 : k) * htr
  have hH : ∃ u, Ω u - α • u ≠ 0 := by
    by_contra h; push Not at h
    have hΩeq : Ω = α • LinearMap.id := LinearMap.ext fun v => by simpa [sub_eq_zero] using h v
    rw [hΩeq, map_smul, LinearMap.trace_id, h2, smul_eq_mul] at htr
    apply hne; linear_combination htr
  obtain ⟨u, hu⟩ := hG
  obtain ⟨u', hu'⟩ := hH
  refine ⟨Ω u - α' • u, Ω u' - α • u', ?_, hu, hu', hΩv u, hΩv' u'⟩
  have hli : LinearIndependent k ![Ω u - α' • u, Ω u' - α • u'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x => Ω x - α' • x) hst
    simp only [map_add, map_smul, hΩv u, hΩv' u', map_zero, smul_zero, sub_zero] at h1

    have h1' : (s * (α - α')) • (Ω u - α' • u) = 0 := by
      rw [← h1]; module
    have hs : s = 0 := by
      rcases mul_eq_zero.mp ((smul_eq_zero.mp h1').resolve_right hu) with hs | hs
      · exact hs
      · exact absurd (sub_eq_zero.mp hs) hne
    subst hs
    simp only [zero_smul, zero_add] at hst
    exact ⟨rfl, (smul_eq_zero.mp hst).resolve_right hu'⟩
  have hspan : ⊤ ≤ Submodule.span k (Set.range ![Ω u - α' • u, Ω u' - α • u']) := by
    have hcard : Fintype.card (Fin 2) = Module.finrank k W := by simp [h2]
    exact (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  intro v
  have hv : v ∈ Submodule.span k (Set.range ![Ω u - α' • u, Ω u' - α • u']) := hspan Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, hc⟩ := hv
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp

theorem swap_coeffs (v₁ v₂ : W) (hspan : ∀ v : W, ∃ s t : k, v = s • v₁ + t • v₂) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0)
    (Ω P : W →ₗ[k] W) (α α' : k) (hne : α ≠ α') (hΩ₁ : Ω v₁ = α • v₁) (hΩ₂ : Ω v₂ = α' • v₂)
    (hPΩ : P ∘ₗ Ω = ((α + α') • LinearMap.id - Ω) ∘ₗ P) :
    ∃ β γ : k, P v₁ = β • v₂ ∧ P v₂ = γ • v₁ := by
  have hc : ∀ v, P (Ω v) = (α + α') • P v - Ω (P v) := fun v => by
    have := congrArg (fun f : W →ₗ[k] W => f v) hPΩ
    simpa using this
  obtain ⟨s, t, hst⟩ := hspan (P v₁)
  obtain ⟨s', t', hst'⟩ := hspan (P v₂)
  have a1 := hc v₁
  rw [hΩ₁, map_smul, hst, map_add, map_smul, map_smul, hΩ₁, hΩ₂] at a1

  have e1 : (s * (α - α')) • v₁ = 0 := by
    have := sub_eq_zero.mpr a1
    rw [← this]; module
  have hs : s = 0 := by
    rcases mul_eq_zero.mp ((smul_eq_zero.mp e1).resolve_right hv₁) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne
  have a2 := hc v₂
  rw [hΩ₂, map_smul, hst', map_add, map_smul, map_smul, hΩ₁, hΩ₂] at a2
  have e2 : (t' * (α' - α)) • v₂ = 0 := by
    have := sub_eq_zero.mpr a2
    rw [← this]; module
  have ht' : t' = 0 := by
    rcases mul_eq_zero.mp ((smul_eq_zero.mp e2).resolve_right hv₂) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hne
  refine ⟨t, s', ?_, ?_⟩
  · rw [hst, hs, zero_smul, zero_add]
  · rw [hst', ht', zero_smul, add_zero]

theorem kill (v₁ v₂ : W) (hspan : ∀ v : W, ∃ s t : k, v = s • v₁ + t • v₂)
    (Ω P L : W →ₗ[k] W) (α α' : k) (hne : α ≠ α') (hΩ₁ : Ω v₁ = α • v₁) (hΩ₂ : Ω v₂ = α' • v₂)
    (β γ : k) (hP₁ : P v₁ = β • v₂) (hP₂ : P v₂ = γ • v₁) (hβγ : β * γ = 0)
    (bf : W →ₗ[k] W →ₗ[k] k) (halt : ∀ v, bf v v = 0)
    (hbal : ∀ v w : W, bf v (Ω w) = bf ((Ω + P ∘ₗ L) v) w) : bf = 0 := by
  have h11 := halt v₁
  have h22 := halt v₂
  have h21 : bf v₂ v₁ = -bf v₁ v₂ := by
    have h := halt (v₁ + v₂)
    simp only [map_add, LinearMap.add_apply, h11, h22, zero_add, add_zero] at h
    linear_combination h
  obtain ⟨l₁₁, l₂₁, hL₁⟩ := hspan (L v₁)
  obtain ⟨l₁₂, l₂₂, hL₂⟩ := hspan (L v₂)
  have e1 := hbal v₁ v₂
  have e2 := hbal v₂ v₁
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hΩ₁, hΩ₂, map_smul, map_add, LinearMap.smul_apply,
    smul_eq_mul, h11, h22] at e1 e2
  rw [hL₁] at e1
  rw [hL₂] at e2
  simp only [map_add, map_smul, hP₁, hP₂, smul_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h11, h22, h21, mul_zero, add_zero, zero_add, mul_neg] at e1 e2
  by_contra hbf
  have h12 : bf v₁ v₂ ≠ 0 := by
    intro h12
    exact hbf (bf_eq_zero_of_span v₁ v₂ hspan bf h11 h12 (by rw [h21, h12, neg_zero]) h22)
  have hγ : γ ≠ 0 := by
    rintro rfl
    apply hne
    have : (α' - α) * bf v₁ v₂ = 0 := by linear_combination e1
    have := (mul_eq_zero.mp this).resolve_right h12
    linear_combination -this
  have hβ : β ≠ 0 := by
    rintro rfl
    apply hne
    have : (α - α') * bf v₁ v₂ = 0 := by linear_combination (-1 : k) * e2
    have := (mul_eq_zero.mp this).resolve_right h12
    linear_combination this
  exact mul_ne_zero hβ hγ hβγ

end RKcore

namespace RKmain
open QuaternionAlgebra

theorem exists_roots (k : Type) [Field k] [IsAlgClosed k] {p : ℕ} [Fact p.Prime] [CharP k p] (t n : ℤ)
    (hdisc : (t : ZMod p) ^ 2 - 4 * (n : ZMod p) ≠ 0) :
    ∃ α α' : k, α ≠ α' ∧ α + α' = (t : k) ∧ α * α' = (n : k) := by
  have hdk : (t : k) ^ 2 - 4 * (n : k) ≠ 0 := by
    intro h
    apply hdisc
    apply (ZMod.castHom (dvd_refl p) k).injective
    simp [map_sub, map_mul, map_pow, map_intCast, map_ofNat, h]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (Polynomial.C (1 : k) * Polynomial.X ^ 2 + Polynomial.C (-(t : k)) * Polynomial.X + Polynomial.C (n : k))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, one_mul] at hα
  refine ⟨α, (t : k) - α, ?_, by ring, by linear_combination (-1 : k) * hα⟩
  intro h
  apply hdk
  linear_combination (-4 : k) * hα + (2 * α - (t : k)) * h

theorem main
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y)
    (htr : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k W (Ψ m) = (n : k))
    (bf : W →ₗ[k] W →ₗ[k] k)
    (hbal : ∀ (x : ↥Λ) (v w : W), bf v (Ψ x w) = bf (Ψ (star x) v) w)
    (halt : ∀ v : W, bf v v = 0) :
    bf = 0 := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := hO.one_mem
  obtain ⟨ω, hω, t, n, hta, htn, -, hdisc, ⟨z, hz, hb⟩, -, ⟨l₁, l₂, hl₁, hl₂, hd⟩, -, -, -⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq
      hqq' hB Λ hΛ μ hμ star hstar hp

  obtain ⟨ωΛ, rfl⟩ : ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) = ω := ⟨⟨ω, hω⟩, rfl⟩
  obtain ⟨zΛ, rfl⟩ : ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) = z := ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨l₁Λ, rfl⟩ : ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) = l₁ := ⟨⟨l₁, hl₁⟩, rfl⟩
  obtain ⟨l₂Λ, rfl⟩ : ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) = l₂ := ⟨⟨l₂, hl₂⟩, rfl⟩
  obtain ⟨one, hone⟩ : ∃ x : ↥Λ, (x : ℍ[ℚ, a, b]) = 1 := ⟨⟨1, h1⟩, rfl⟩
  simp only [Subtype.coe_eta] at hd

  let ΨZ : ↥Λ →+ (W →ₗ[k] W) := AddMonoidHom.mk' Ψ hΨ_add
  have hΨZ : ∀ x, ΨZ x = Ψ x := fun _ => rfl
  have Ψ_zsmul : ∀ (m : ℤ) (x : ↥Λ), Ψ (m • x) = (m : k) • Ψ x := fun m x => by
    rw [← hΨZ, map_zsmul, hΨZ, Int.cast_smul_eq_zsmul]
  have Ψ_nsmul : ∀ (m : ℕ) (x : ↥Λ), Ψ (m • x) = (m : k) • Ψ x := fun m x => by
    rw [← hΨZ, map_nsmul, hΨZ, Nat.cast_smul_eq_nsmul]
  have Ψ_sub : ∀ x y : ↥Λ, Ψ (x - y) = Ψ x - Ψ y := fun x y => by rw [← hΨZ, map_sub]; rfl
  have Ψ_neg : ∀ x : ↥Λ, Ψ (-x) = -Ψ x := fun x => by rw [← hΨZ, map_neg]; rfl
  have Ψ_p : ∀ x : ↥Λ, Ψ (p • x) = 0 := fun x => by
    rw [Ψ_nsmul, CharP.cast_eq_zero, zero_smul]
  have hΨ1 : Ψ one = LinearMap.id := by
    rw [show one = ⟨1, h1⟩ from Subtype.ext hone]; exact hΨ_one h1
  have hΨt : ∀ m : ℤ, Ψ (m • one) = (m : k) • LinearMap.id := fun m => by rw [Ψ_zsmul, hΨ1]

  obtain ⟨α, α', hne, hsum, hprod⟩ := exists_roots k t n hdisc

  have hcastt : ((t : ℚ) : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) := by
    rw [Int.smul_one_eq_cast]; norm_cast
  have hcastn : ((n : ℚ) : ℍ[ℚ, a, b]) = n • (1 : ℍ[ℚ, a, b]) := by
    rw [Int.smul_one_eq_cast]; norm_cast
  have hta' : Star.star (ωΛ : ℍ[ℚ, a, b]) = t • (1 : ℍ[ℚ, a, b]) - ωΛ := by
    rw [← hcastt, ← hta]; abel
  have hstar_coe : ((t • one - ωΛ : ↥Λ) : ℍ[ℚ, a, b]) = Star.star (ωΛ : ℍ[ℚ, a, b]) := by
    rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, hone, hta']
  have hm : (ωΛ : ℍ[ℚ, a, b]) * ((t • one - ωΛ : ↥Λ) : ℍ[ℚ, a, b]) ∈ Λ := hO.mul_mem ωΛ.2 (t • one - ωΛ).2
  have key := hΨ_mul ωΛ (t • one - ωΛ) hm
  have hL : (⟨(ωΛ : ℍ[ℚ, a, b]) * ((t • one - ωΛ : ↥Λ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = n • one := by
    apply Subtype.ext
    show (ωΛ : ℍ[ℚ, a, b]) * ((t • one - ωΛ : ↥Λ) : ℍ[ℚ, a, b]) = ((n • one : ↥Λ) : ℍ[ℚ, a, b])
    rw [hstar_coe, htn, Submodule.coe_smul_of_tower, hone]
    exact hcastn
  have hΩ2 : Ψ ωΛ ∘ₗ ((t : k) • LinearMap.id - Ψ ωΛ) = (n : k) • LinearMap.id := by
    rw [← hΨt t, ← Ψ_sub, ← key, hL, hΨt]
  have hΩv : ∀ v, Ψ ωΛ (Ψ ωΛ v) = (t : k) • Ψ ωΛ v - (n : k) • v := fun v => by
    have := congrArg (fun f : W →ₗ[k] W => f v) hΩ2
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub,
      map_smul] at this
    rw [← this]; abel
  have hΩquad : (Ψ ωΛ - α • LinearMap.id) ∘ₗ (Ψ ωΛ - α' • LinearMap.id) = 0 := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul,
      LinearMap.zero_apply, hΩv]
    rw [← hsum, ← hprod]
    module

  have htrΩ : LinearMap.trace k W (Ψ ωΛ) = α + α' := by
    rw [hsum]; exact htr ωΛ t hta

  obtain ⟨v₁, v₂, hspan, hv₁, hv₂, hΩ₁, hΩ₂⟩ := RKcore.eigenbasis_of_quadratic hW (Ψ ωΛ) α α' hne hΩquad htrΩ

  have hmμ : (μ : ℍ[ℚ, a, b]) * μ ∈ Λ := hO.mul_mem μ.2 μ.2
  have hμΛ : (⟨(μ : ℍ[ℚ, a, b]) * μ, hmμ⟩ : ↥Λ) = -((q * q' : ℕ) • one) := by
    apply Subtype.ext
    show (μ : ℍ[ℚ, a, b]) * μ = ((-((q * q' : ℕ) • one) : ↥Λ) : ℍ[ℚ, a, b])
    rw [hμ, Submodule.coe_neg, Submodule.coe_smul_of_tower, hone, Nat.cast_smul_eq_nsmul]
  have hq0 : ((q * q' : ℕ) : k) = 0 := by
    rw [CharP.cast_eq_zero_iff k p]
    rcases hp with rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hPP : Ψ μ ∘ₗ Ψ μ = 0 := by
    rw [← hΨ_mul μ μ hmμ, hμΛ, Ψ_neg, Ψ_nsmul, hΨ1, hq0, zero_smul, neg_zero]

  have hm1 : (μ : ℍ[ℚ, a, b]) * ωΛ ∈ Λ := hO.mul_mem μ.2 ωΛ.2
  have hm2 : (ωΛ : ℍ[ℚ, a, b]) * μ ∈ Λ := hO.mul_mem ωΛ.2 μ.2
  have elt : (⟨(μ : ℍ[ℚ, a, b]) * ωΛ, hm1⟩ : ↥Λ) + ⟨(ωΛ : ℍ[ℚ, a, b]) * μ, hm2⟩ - t • μ = p • zΛ := by
    apply Subtype.ext
    show (μ : ℍ[ℚ, a, b]) * ωΛ + ωΛ * μ - ((t • μ : ↥Λ) : ℍ[ℚ, a, b]) = ((p • zΛ : ↥Λ) : ℍ[ℚ, a, b])
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ,
      ← Nat.cast_smul_eq_nsmul ℚ]
    exact hb
  have hPΩ : Ψ μ ∘ₗ Ψ ωΛ = ((α + α') • LinearMap.id - Ψ ωΛ) ∘ₗ Ψ μ := by
    have e := congrArg Ψ elt
    rw [Ψ_sub, hΨ_add, hΨ_mul μ ωΛ hm1, hΨ_mul ωΛ μ hm2, Ψ_zsmul, Ψ_p] at e
    rw [hsum, LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.id_comp, ← sub_eq_zero, ← e]
    abel
  obtain ⟨β, γ, hP₁, hP₂⟩ := RKcore.swap_coeffs v₁ v₂ hspan hv₁ hv₂ (Ψ ωΛ) (Ψ μ) α α' hne hΩ₁ hΩ₂ hPΩ
  have hβγ : β * γ = 0 := by
    have := congrArg (fun f : W →ₗ[k] W => f v₁) hPP
    simp only [LinearMap.comp_apply, hP₁, map_smul, hP₂, smul_smul, LinearMap.zero_apply] at this
    exact (smul_eq_zero.mp this).resolve_right hv₁

  have hml : (μ : ℍ[ℚ, a, b]) * l₂Λ ∈ Λ := hO.mul_mem μ.2 l₂Λ.2
  have hstar_elt : star ωΛ = ωΛ + p • l₁Λ + ⟨(μ : ℍ[ℚ, a, b]) * l₂Λ, hml⟩ := by
    apply Subtype.ext
    show ((star ωΛ : ↥Λ) : ℍ[ℚ, a, b]) = ωΛ + ((p • l₁Λ : ↥Λ) : ℍ[ℚ, a, b]) + μ * l₂Λ
    rw [hd, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]
  have hΨstar : Ψ (star ωΛ) = Ψ ωΛ + Ψ μ ∘ₗ Ψ l₂Λ := by
    rw [hstar_elt, hΨ_add, hΨ_add, Ψ_p, add_zero, hΨ_mul μ l₂Λ hml]

  refine RKcore.kill v₁ v₂ hspan (Ψ ωΛ) (Ψ μ) (Ψ l₂Λ) α α' hne hΩ₁ hΩ₂ β γ hP₁ hP₂ hβγ bf halt fun v w => ?_
  rw [← hΨstar]
  exact hbal ωΛ v w

end RKmain

open QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    {p : ℕ} [Fact p.Prime] (hp : p = q ∨ p = q')
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (W : Type) [AddCommGroup W] [Module k W] [Module.Finite k W] (hW : Module.finrank k W = 2)
    (Ψ : ↥Λ → (W →ₗ[k] W))
    (hΨ_add : ∀ x y : ↥Λ, Ψ (x + y) = Ψ x + Ψ y)
    (hΨ_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, Ψ ⟨1, h1⟩ = LinearMap.id)
    (hΨ_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      Ψ ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩ = Ψ x ∘ₗ Ψ y)
    (htr : ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) + Star.star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k W (Ψ m) = (n : k))
    (bf : W →ₗ[k] W →ₗ[k] k)
    (hbal : ∀ (x : ↥Λ) (v w : W), bf v (Ψ x w) = bf (Ψ (star x) v) w)
    (halt : ∀ v : W, bf v v = 0) :
    bf = 0 :=
  RKmain.main hqq' hB Λ hΛ μ hμ star hstar hp k W hW Ψ hΨ_add hΨ_one hΨ_mul htr bf hbal halt

end S_CerednikDrinfeld_SpecialModule_eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialModule_eq_zero_of_forall_apply_apply_eq_apply_star_apply_of_forall_apply_self_eq_zero_of_trace_eq (solution)
