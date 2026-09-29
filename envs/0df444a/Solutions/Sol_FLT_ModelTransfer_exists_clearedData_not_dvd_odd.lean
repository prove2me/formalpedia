-- Prove2me | solution 1 for FLT.ModelTransfer.exists_clearedData_not_dvd_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/20abdc3a-2db1-596a-9173-91812d95579c

import Definitions.Def_ModelTransfer_ClearedData
import Mathlib.Tactic.IntervalCases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd

set_option autoImplicit false
set_option maxHeartbeats 2400000

open WeierstrassCurve

namespace FLT
p2m_export "FLT" "ModelTransfer.ClearedData"
namespace ModelTransfer
p2m_export "FLT.ModelTransfer" "ClearedData"
p2m_open "FLT.ModelTransfer FLT"

section OddLocal

variable {q : ℕ}

private def IsLocalIntAux (q : ℕ) (x : ℚ) : Prop :=
  ∃ a b : ℤ, ¬ (q : ℤ) ∣ b ∧ (b : ℚ) * x = (a : ℚ)

private lemma not_dvd_one_aux (hq : q.Prime) : ¬ (q : ℤ) ∣ (1 : ℤ) := fun h => by
  have h1 : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos h
  have h2 : (1 : ℕ) < q := hq.one_lt
  omega

private lemma IsLocalIntAux.intCast (hq : q.Prime) (n : ℤ) : IsLocalIntAux q ((n : ℤ) : ℚ) :=
  ⟨n, 1, not_dvd_one_aux hq, by push_cast; ring⟩

private lemma IsLocalIntAux.add (hq : q.Prime) {x y : ℚ} (hx : IsLocalIntAux q x)
    (hy : IsLocalIntAux q y) : IsLocalIntAux q (x + y) := by
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := hy
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, fun h => ?_, ?_⟩
  · rcases (Int.Prime.dvd_mul' hq h) with h | h
    exacts [hb₁ h, hb₂ h]
  · push_cast
    linear_combination (b₂ : ℚ) * h₁ + (b₁ : ℚ) * h₂

private lemma IsLocalIntAux.mul (hq : q.Prime) {x y : ℚ} (hx : IsLocalIntAux q x)
    (hy : IsLocalIntAux q y) : IsLocalIntAux q (x * y) := by
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := hx
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := hy
  refine ⟨a₁ * a₂, b₁ * b₂, fun h => ?_, ?_⟩
  · rcases (Int.Prime.dvd_mul' hq h) with h | h
    exacts [hb₁ h, hb₂ h]
  · push_cast
    linear_combination (((b₂ : ℚ)) * y) * h₁ + (a₁ : ℚ) * h₂

private lemma IsLocalIntAux.neg {x : ℚ} (hx : IsLocalIntAux q x) : IsLocalIntAux q (-x) := by
  obtain ⟨a, b, hb, h⟩ := hx
  exact ⟨-a, b, hb, by push_cast; linear_combination -h⟩

private lemma IsLocalIntAux.sub (hq : q.Prime) {x y : ℚ} (hx : IsLocalIntAux q x)
    (hy : IsLocalIntAux q y) : IsLocalIntAux q (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hq hy.neg

private lemma IsLocalIntAux.of_intCast_mul (hq : q.Prime) {c : ℤ} (hc : ¬ (q : ℤ) ∣ c) {x : ℚ}
    (h : IsLocalIntAux q ((c : ℚ) * x)) : IsLocalIntAux q x := by
  obtain ⟨a, b, hb, hab⟩ := h
  refine ⟨a, c * b, fun hd => ?_, by push_cast; linear_combination hab⟩
  rcases (Int.Prime.dvd_mul' hq hd) with h | h
  exacts [hc h, hb h]

variable {V W : WeierstrassCurve ℤ} {C : VariableChange ℚ}

private lemma delta_num_den_identity'
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    W.Δ * ((C.u : ℚ)).num ^ 12 = V.Δ * (((C.u : ℚ)).den : ℤ) ^ 12 := by
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have hΔQ : ((W.Δ : ℤ) : ℚ) = ((C.u : ℚ))⁻¹ ^ 12 * ((V.Δ : ℤ) : ℚ) := by
    have h1 : (W.map (Int.castRingHom ℚ)).Δ = (C • (V.map (Int.castRingHom ℚ))).Δ := by
      rw [hC]
    rw [variableChange_Δ, map_Δ, map_Δ] at h1
    simpa [Units.val_inv_eq_inv_val, eq_intCast] using h1
  have hden : (((C.u : ℚ)).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (C.u : ℚ).den_nz
  have hnum : ((C.u : ℚ)) * (((C.u : ℚ)).den : ℚ) = (((C.u : ℚ)).num : ℚ) :=
    (eq_div_iff hden).mp (Rat.num_div_den _).symm
  have hpow : ((((C.u : ℚ)).num : ℤ) : ℚ) ^ 12
      = ((C.u : ℚ)) ^ 12 * ((((C.u : ℚ)).den : ℕ) : ℚ) ^ 12 := by
    rw [← hnum]
    ring
  have key : ((W.Δ * ((C.u : ℚ)).num ^ 12 : ℤ) : ℚ)
      = ((V.Δ * (((C.u : ℚ)).den : ℤ) ^ 12 : ℤ) : ℚ) := by
    push_cast
    push_cast at hpow
    rw [hpow, hΔQ]
    field_simp
  exact_mod_cast key

private lemma not_dvd_num_u' (hq : q.Prime)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) : ¬ (q : ℤ) ∣ ((C.u : ℚ)).num := by
  intro hdvd
  have hkey := delta_num_den_identity' hC
  have hdvdL : (q : ℤ) ∣ V.Δ * (((C.u : ℚ)).den : ℤ) ^ 12 := by
    rw [← hkey]; exact Dvd.dvd.mul_left (hdvd.pow (by norm_num)) _
  rcases Int.Prime.dvd_mul' hq hdvdL with h | h
  · exact hV h
  · have hd : (q : ℤ) ∣ (((C.u : ℚ)).den : ℤ) := Int.Prime.dvd_pow' hq h
    have hcop := (C.u : ℚ).reduced
    have : (q : ℕ) ∣ Nat.gcd ((C.u : ℚ)).num.natAbs ((C.u : ℚ)).den :=
      Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd))
        (Int.natCast_dvd_natCast.mp (by simpa using hd))
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one this)

private lemma not_dvd_den_u' (hq : q.Prime)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ¬ (q : ℤ) ∣ ((((C.u : ℚ)).den : ℕ) : ℤ) := by
  intro hdvd
  have hkey := delta_num_den_identity' hC
  have hdvdR : (q : ℤ) ∣ W.Δ * ((C.u : ℚ)).num ^ 12 := by
    rw [hkey]; exact Dvd.dvd.mul_left (hdvd.pow (by norm_num)) _
  rcases Int.Prime.dvd_mul' hq hdvdR with h | h
  · exact hW h
  · exact not_dvd_num_u' hq hC hV (Int.Prime.dvd_pow' hq h)

private lemma isLocalIntAux_u (hq : q.Prime)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) : IsLocalIntAux q ((C.u : ℚ)) := by
  refine ⟨((C.u : ℚ)).num, ((((C.u : ℚ)).den : ℕ) : ℤ), not_dvd_den_u' hq hC hV hW, ?_⟩
  have hden : (((C.u : ℚ)).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (C.u : ℚ).den_nz
  have hnum : ((C.u : ℚ)) * (((C.u : ℚ)).den : ℚ) = (((C.u : ℚ)).num : ℚ) :=
    (eq_div_iff hden).mp (Rat.num_div_den _).symm
  push_cast
  linarith [hnum]

private lemma isLocalIntAux_u_inv (hq : q.Prime)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) : IsLocalIntAux q (((C.u : ℚ))⁻¹) := by
  refine ⟨((((C.u : ℚ)).den : ℕ) : ℤ), ((C.u : ℚ)).num, not_dvd_num_u' hq hC hV, ?_⟩
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have hden : (((C.u : ℚ)).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (C.u : ℚ).den_nz
  have hnum : ((C.u : ℚ)) * (((C.u : ℚ)).den : ℚ) = (((C.u : ℚ)).num : ℚ) :=
    (eq_div_iff hden).mp (Rat.num_div_den _).symm
  push_cast
  field_simp
  linarith [hnum]

private lemma a1_formula' (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₁ : ℚ) = ((C.u : ℚ))⁻¹ * ((V.a₁ : ℚ) + 2 * C.s) := by
  have h := congrArg WeierstrassCurve.a₁ hC
  simp only [variableChange_def, map_a₁, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma a3_formula' (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.a₃ : ℚ) = ((C.u : ℚ))⁻¹ ^ 3 *
      ((V.a₃ : ℚ) + C.r * (V.a₁ : ℚ) + 2 * C.t) := by
  have h := congrArg WeierstrassCurve.a₃ hC
  simp only [variableChange_def, map_a₁, map_a₃, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma b6_formula' (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    (W.b₆ : ℚ) = ((C.u : ℚ))⁻¹ ^ 6 *
      ((V.b₆ : ℚ) + 2 * C.r * (V.b₄ : ℚ) + C.r ^ 2 * (V.b₂ : ℚ) + 4 * C.r ^ 3) := by
  have h : (C • (V.map (Int.castRingHom ℚ))).b₆ = (W.map (Int.castRingHom ℚ)).b₆ := by
    rw [hC]
  rw [variableChange_b₆] at h
  simp only [map_b₂, map_b₄, map_b₆, eq_intCast, Units.val_inv_eq_inv_val] at h
  exact h.symm

private lemma b6_cleared' (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ)) :
    ((C.u : ℚ)) ^ 6 * (W.b₆ : ℚ)
      = (V.b₆ : ℚ) + 2 * C.r * (V.b₄ : ℚ) + C.r ^ 2 * (V.b₂ : ℚ) + 4 * C.r ^ 3 := by
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  rw [b6_formula' hC, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]

private lemma not_dvd_two' (hq : q.Prime) (hq2 : q ≠ 2) : ¬ (q : ℤ) ∣ (2 : ℤ) := by
  intro h
  have h' : q ∣ 2 := by exact_mod_cast h
  have hle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h'
  interval_cases q
  · exact absurd hq (by decide)
  · exact absurd hq (by decide)
  · exact hq2 rfl

private lemma not_dvd_four' (hq : q.Prime) (hq2 : q ≠ 2) : ¬ (q : ℤ) ∣ (4 : ℤ) := by
  intro h
  have h' : q ∣ 4 := by exact_mod_cast h
  have hle : q ≤ 4 := Nat.le_of_dvd (by norm_num) h'
  interval_cases q <;>
    first
      | exact absurd hq (by decide)
      | exact absurd h' (by decide)
      | exact hq2 rfl

private lemma isLocalIntAux_two_s (hq : q.Prime)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    IsLocalIntAux q ((2 : ℚ) * C.s) := by
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have h1' : ((C.u : ℚ)) * (W.a₁ : ℚ) = (V.a₁ : ℚ) + 2 * C.s := by
    have h := a1_formula' hC
    field_simp at h
    linear_combination h
  have key : (2 : ℚ) * C.s = ((C.u : ℚ)) * (W.a₁ : ℚ) - (V.a₁ : ℚ) := by
    linarith [h1']
  rw [key]
  exact ((isLocalIntAux_u hq hC hV hW).mul hq (.intCast hq W.a₁)).sub hq (.intCast hq V.a₁)

private lemma isLocalIntAux_s (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) : IsLocalIntAux q C.s := by
  have := isLocalIntAux_two_s hq hC hV hW
  exact IsLocalIntAux.of_intCast_mul hq (not_dvd_two' hq hq2) (by exact_mod_cast this)

private lemma isLocalIntAux_r_odd (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) : IsLocalIntAux q C.r := by
  obtain ⟨A, B, hB, hAB⟩ := isLocalIntAux_u hq hC hV hW
  have hdenQ : ((C.r.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr C.r.den_nz

  have hn : ((C.r.den : ℕ) : ℚ) * C.r = ((C.r.num : ℤ) : ℚ) := by
    rw [mul_comm]
    exact (eq_div_iff hdenQ).mp (Rat.num_div_den _).symm
  refine ⟨C.r.num, ((C.r.den : ℕ) : ℤ), ?_, by push_cast; exact hn⟩

  intro hdvd

  have h6 : ((B : ℤ) : ℚ) ^ 6 * ((C.u : ℚ)) ^ 6 = ((A : ℤ) : ℚ) ^ 6 := by
    rw [← mul_pow, hAB]
  have hn2 : ((C.r.den : ℕ) : ℚ) ^ 2 * C.r ^ 2 = ((C.r.num : ℤ) : ℚ) ^ 2 := by
    rw [← mul_pow, hn]
  have hn3 : ((C.r.den : ℕ) : ℚ) ^ 3 * C.r ^ 3 = ((C.r.num : ℤ) : ℚ) ^ 3 := by
    rw [← mul_pow, hn]
  have hb6c := b6_cleared' hC

  have hkey : A ^ 6 * (C.r.den : ℤ) ^ 3 * W.b₆
      = B ^ 6 * (C.r.den : ℤ) ^ 3 * V.b₆ + 2 * B ^ 6 * C.r.num * (C.r.den : ℤ) ^ 2 * V.b₄
        + B ^ 6 * C.r.num ^ 2 * (C.r.den : ℤ) * V.b₂ + 4 * B ^ 6 * C.r.num ^ 3 := by
    have hcast : ((A ^ 6 * (C.r.den : ℤ) ^ 3 * W.b₆ : ℤ) : ℚ)
        = ((B ^ 6 * (C.r.den : ℤ) ^ 3 * V.b₆ + 2 * B ^ 6 * C.r.num * (C.r.den : ℤ) ^ 2 * V.b₄
            + B ^ 6 * C.r.num ^ 2 * (C.r.den : ℤ) * V.b₂ + 4 * B ^ 6 * C.r.num ^ 3 : ℤ) : ℚ) := by
      push_cast
      linear_combination
        (-(((C.r.den : ℕ) : ℚ) ^ 3 * (W.b₆ : ℚ))) * h6
          + ((B : ℚ) ^ 6 * ((C.r.den : ℕ) : ℚ) ^ 3) * hb6c
          + (2 * (B : ℚ) ^ 6 * ((C.r.den : ℕ) : ℚ) ^ 2 * (V.b₄ : ℚ)) * hn
          + ((B : ℚ) ^ 6 * ((C.r.den : ℕ) : ℚ) * (V.b₂ : ℚ)) * hn2
          + (4 * (B : ℚ) ^ 6) * hn3
    exact_mod_cast hcast

  have heq : 4 * B ^ 6 * C.r.num ^ 3
      = (C.r.den : ℤ) * (A ^ 6 * (C.r.den : ℤ) ^ 2 * W.b₆ - B ^ 6 * (C.r.den : ℤ) ^ 2 * V.b₆
          - 2 * B ^ 6 * C.r.num * (C.r.den : ℤ) * V.b₄ - B ^ 6 * C.r.num ^ 2 * V.b₂) := by
    linear_combination -hkey
  have h4 : (q : ℤ) ∣ 4 * B ^ 6 * C.r.num ^ 3 := by
    rw [heq]
    exact hdvd.mul_right _
  rcases Int.Prime.dvd_mul' hq h4 with h45 | hm3
  · rcases Int.Prime.dvd_mul' hq h45 with h44 | hB6
    · exact not_dvd_four' hq hq2 h44
    · exact hB (Int.Prime.dvd_pow' hq hB6)
  ·
    have hqm : (q : ℤ) ∣ C.r.num := Int.Prime.dvd_pow' hq hm3
    have hcop := C.r.reduced
    have : (q : ℕ) ∣ Nat.gcd C.r.num.natAbs C.r.den :=
      Nat.dvd_gcd (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hqm))
        (Int.natCast_dvd_natCast.mp (by simpa using hdvd))
    rw [hcop] at this
    exact hq.one_lt.ne' (Nat.eq_one_of_dvd_one this)

private lemma isLocalIntAux_t_odd (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) : IsLocalIntAux q C.t := by
  have hu : ((C.u : ℚ)) ≠ 0 := C.u.ne_zero
  have h3' : ((C.u : ℚ)) ^ 3 * (W.a₃ : ℚ)
      = (V.a₃ : ℚ) + C.r * (V.a₁ : ℚ) + 2 * C.t := by
    have h := a3_formula' hC
    field_simp at h
    linear_combination h
  have key : (2 : ℚ) * C.t
      = ((C.u : ℚ)) * ((C.u : ℚ)) * ((C.u : ℚ)) * (W.a₃ : ℚ)
        - ((V.a₃ : ℚ) + C.r * (V.a₁ : ℚ)) := by
    linear_combination -h3'
  refine IsLocalIntAux.of_intCast_mul hq (not_dvd_two' hq hq2) ?_
  show IsLocalIntAux q (((2 : ℤ) : ℚ) * C.t)
  have hu' := isLocalIntAux_u hq hC hV hW
  have hr := isLocalIntAux_r_odd hq hq2 hC hV hW
  have : IsLocalIntAux q ((2 : ℚ) * C.t) := by
    rw [key]
    exact (((hu'.mul hq hu').mul hq hu').mul hq (.intCast hq W.a₃)).sub hq
      ((IsLocalIntAux.intCast hq V.a₃).add hq (hr.mul hq (.intCast hq V.a₁)))
  exact_mod_cast this

end OddLocal

end FLT.ModelTransfer

p2m_open "WeierstrassCurve FLT.ModelTransfer P2MW.S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd.FLT.ModelTransfer"

theorem solution {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ∃ D : FLT.ModelTransfer.ClearedData C, ¬ q ∣ D.N := by
  obtain ⟨a₁, b₁, hb₁, h₁⟩ := isLocalIntAux_u hq hC hV hW
  obtain ⟨a₂, b₂, hb₂, h₂⟩ := isLocalIntAux_u_inv hq hC hV
  obtain ⟨a₃, b₃, hb₃, h₃⟩ := isLocalIntAux_r_odd hq hq2 hC hV hW
  obtain ⟨a₄, b₄, hb₄, h₄⟩ := isLocalIntAux_s hq hq2 hC hV hW
  obtain ⟨a₅, b₅, hb₅, h₅⟩ := isLocalIntAux_t_odd hq hq2 hC hV hW
  have hPq : ¬ (q : ℤ) ∣ b₁ * b₂ * b₃ * b₄ * b₅ := by
    intro h
    rcases Int.Prime.dvd_mul' hq h with h | h
    · rcases Int.Prime.dvd_mul' hq h with h | h
      · rcases Int.Prime.dvd_mul' hq h with h | h
        · rcases Int.Prime.dvd_mul' hq h with h | h
          exacts [hb₁ h, hb₂ h]
        · exact hb₃ h
      · exact hb₄ h
    · exact hb₅ h
  have hPne : b₁ * b₂ * b₃ * b₄ * b₅ ≠ 0 := fun h => hPq (h ▸ dvd_zero _)
  have hcast : ((((b₁ * b₂ * b₃ * b₄ * b₅) ^ 2).toNat : ℕ) : ℚ)
      = (((b₁ * b₂ * b₃ * b₄ * b₅ : ℤ) : ℚ)) ^ 2 := by
    have h0 : (((b₁ * b₂ * b₃ * b₄ * b₅) ^ 2).toNat : ℤ) = (b₁ * b₂ * b₃ * b₄ * b₅) ^ 2 :=
      Int.toNat_of_nonneg (sq_nonneg _)
    exact_mod_cast h0
  refine ⟨{ N := ((b₁ * b₂ * b₃ * b₄ * b₅) ^ 2).toNat
            hN := by
              simp only [ne_eq, Int.toNat_eq_zero, not_le]
              positivity
            U := (b₁ * b₂ * b₃ * b₄ * b₅) * (b₂ * b₃ * b₄ * b₅) * a₁
            U' := (b₁ * b₂ * b₃ * b₄ * b₅) * (b₁ * b₃ * b₄ * b₅) * a₂
            R := (b₁ * b₂ * b₃ * b₄ * b₅) * (b₁ * b₂ * b₄ * b₅) * a₃
            S := (b₁ * b₂ * b₃ * b₄ * b₅) * (b₁ * b₂ * b₃ * b₅) * a₄
            T := (b₁ * b₂ * b₃ * b₄ * b₅) * (b₁ * b₂ * b₃ * b₄) * a₅
            hU := ?_, hU' := ?_, hR := ?_, hS := ?_, hT := ?_ }, ?_⟩
  · rw [hcast]
    push_cast
    linear_combination (-(b₁ : ℚ) * b₂ ^ 2 * b₃ ^ 2 * b₄ ^ 2 * b₅ ^ 2) * h₁
  · rw [hcast]
    push_cast
    linear_combination (-(b₁ : ℚ) ^ 2 * b₂ * b₃ ^ 2 * b₄ ^ 2 * b₅ ^ 2) * h₂
  · rw [hcast]
    push_cast
    linear_combination (-(b₁ : ℚ) ^ 2 * b₂ ^ 2 * b₃ * b₄ ^ 2 * b₅ ^ 2) * h₃
  · rw [hcast]
    push_cast
    linear_combination (-(b₁ : ℚ) ^ 2 * b₂ ^ 2 * b₃ ^ 2 * b₄ * b₅ ^ 2) * h₄
  · rw [hcast]
    push_cast
    linear_combination (-(b₁ : ℚ) ^ 2 * b₂ ^ 2 * b₃ ^ 2 * b₄ ^ 2 * b₅) * h₅
  · intro h
    have hd : (q : ℤ) ∣ (b₁ * b₂ * b₃ * b₄ * b₅) ^ 2 := by
      have := Int.natCast_dvd_natCast.mpr h
      rwa [Int.toNat_of_nonneg (sq_nonneg _)] at this
    exact hPq (Int.Prime.dvd_pow' hq hd)

end S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd
end P2MW
export P2MW.S_FLT_ModelTransfer_exists_clearedData_not_dvd_odd (solution)
