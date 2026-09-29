-- Prove2me | solution 1 for GT.K_le
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T10:37:08.198984+00:00
-- url     : https://prove2.me/submissions/c7fb9c6e-da38-4b03-b0f9-d852197b95dc

import Mathlib
import Definitions.Def_GreenTaoFourCore

section File_GT_WeylStep
/-!
# The Weyl step of Proposition 7.1 (Green–Tao, Lemmas 3.2 and 7.2)

A poorly distributed label produces a non-zero frequency `k = (k₀, k₁, k₂)` with coordinates
`|k_{j,i}| ≲ (d/η)‖v_i‖` such that `E e(k₀·Ξ(a) + k₁·Ξ(a+r) + k₂·Ξ(a+2r))` is large.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

namespace DTorus

lemma Good.one_le_norm {G : DTorus} (hG : G.Good) (i : Fin G.d) : 1 ≤ ‖G.v i‖ := by
  classical
  have h := hG.2.1 (Pi.single i 1 : Fin G.d → ℤ) (by simp)
  have e : G.emb (fun j => (((Pi.single i 1 : Fin G.d → ℤ) j : ℤ) : ℝ)) = G.v i := by
    unfold emb
    rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rwa [e] at h

end DTorus

end

end GT
end File_GT_WeylStep

section File_GT_Prop71
/-!
# Proposition 7.1 of Green–Tao

A poorly distributed label gives a primitive dual frequency `k'`, a multiplier `m`, and for each
base point `a` of the Bohr set a frequency `ξ_a`, such that `k'·(Ξ(a + 2mh) − Ξ(a))` is small
for `h` in a small Bohr set with frequencies `S ∪ {ξ_a}`.
-/

open Finset KM
open scoped ComplexConjugate

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

variable {S : Finset (ZMod p)} {M : Type*} [AddCommGroup M] {n0 : ZMod p} {ρ : ℝ}
  {Ξ : ZMod p → M}

lemma one_le_wM {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (i : Fin G.d) :
    1 ≤ wM G η i := by
  have h1 := hG.one_le_norm i
  have h2 : (1 : ℝ) ≤ 1000 * (G.d + 1) / η * ‖G.v i‖ := by
    have : (1 : ℝ) ≤ 1000 * (G.d + 1) / η := by
      rw [le_div_iff₀ hη]; have : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _; nlinarith
    nlinarith
  have := h2.trans (Nat.le_ceil _)
  unfold wM
  exact_mod_cast this

lemma one_le_wP {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 1 ≤ wP G η := by
  unfold wP
  refine one_le_pow₀ ?_
  calc (1 : ℝ) = ∏ _i : Fin G.d, (1 : ℝ) := by simp
    _ ≤ ∏ i, (2 * wM G η i : ℝ) := Finset.prod_le_prod (fun _ _ => zero_le_one) fun i _ => by
        have := one_le_wM hG hη hη1 i
        have : (1 : ℝ) ≤ wM G η i := by exact_mod_cast this
        linarith

lemma wδ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < wδ G η := by
  unfold wδ; have := one_le_wP hG hη hη1; positivity

lemma p71δ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < p71δ G η := by
  unfold p71δ; have := wδ_pos hG hη hη1; positivity

end

end GT
end File_GT_Prop71

section File_GT_BadDimNum
/-!
# Numerical bounds for Theorem 6.7
-/

open Finset KM

namespace GT

noncomputable section

variable {p : ℕ} [NeZero p]

/-! ### Generalities -/

lemma le_exp_self' (x : ℝ) : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]

lemma gt_consts : C2 = 4294967296 ∧ 8 * C2 + 100 ≤ C3 ∧ 4 * C3 + 100 ≤ C4 ∧ 2 * C4 + 2 ≤ C5 := by
  refine ⟨by unfold C2; norm_num, by unfold C2 C3; norm_num, ?_, ?_⟩
  · have h1 : C4 = C3 * 2 ^ 192 := by unfold C3 C4; rw [← pow_add]
    have h2 : 8 ≤ 2 ^ 192 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 192 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h3 : 100 ≤ C3 := by unfold C3; norm_num
    generalize 2 ^ 192 = K at h1 h2
    rw [h1]; nlinarith
  · have h1 : C5 = C4 * 2 ^ 768 := by unfold C4 C5; rw [← pow_add]
    have h2 : 4 ≤ 2 ^ 768 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 768 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have h3 : 1 ≤ C4 := by unfold C4; exact Nat.one_le_two_pow
    generalize 2 ^ 768 = K at h1 h2
    rw [h1]; nlinarith

/-- `c u^a ≤ u^b` once `c ≤ u^(b-a)`. -/
lemma mul_pow_le_pow {u c : ℝ} (hu : 1 ≤ u) {a k b : ℕ} (hc : c ≤ u ^ k) (hab : a + k ≤ b) :
    c * u ^ a ≤ u ^ b := by
  calc c * u ^ a ≤ u ^ k * u ^ a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = u ^ (a + k) := by ring
    _ ≤ u ^ b := pow_le_pow_right₀ hu hab

lemma norm_le_vol {G : DTorus} (hG : G.Good) (i : Fin G.d) : ‖G.v i‖ ≤ G.vol := by
  classical
  unfold DTorus.vol
  rw [← Finset.mul_prod_erase _ _ (mem_univ i)]
  have : 1 ≤ ∏ j ∈ univ.erase i, ‖G.v j‖ := by
    calc (1 : ℝ) = ∏ _j ∈ univ.erase i, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun j _ => hG.one_le_norm j
  nlinarith [norm_nonneg (G.v i)]

/-! ### The Weyl cut-offs -/

section wbounds

variable {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {G : DTorus} (hG : G.Good)
  (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3)))
include hη0 hη1 hG hd

lemma u_ge_ten : (10 : ℝ) ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith

omit hG hd in
lemma u_ge_ten' : (10 : ℝ) ≤ 1 / η := by rw [le_div_iff₀ hη0]; linarith

lemma wM_le (i : Fin G.d) : (wM G η i : ℝ) ≤ 1000 * (G.d + 1) * (1 / η) * ‖G.v i‖ + 1 := by
  have := Nat.ceil_lt_add_one (show 0 ≤ 1000 * (G.d + 1) / η * ‖G.v i‖ by positivity)
  unfold wM
  have e : 1000 * (G.d + 1) / η * ‖G.v i‖ = 1000 * (G.d + 1) * (1 / η) * ‖G.v i‖ := by ring
  rw [← e]
  exact this.le

/-- `2000 (d+1) u ≤ u^{2 C₂ + 7}`. -/
lemma poly_d_le : 2000 * ((G.d : ℝ) + 1) * (1 / η) ≤ (1 / η) ^ (2 * C2 + 7) := by
  have hu := u_ge_ten hη0 hη1 hG hd
  have h1 : (1 : ℝ) ≤ (1 / η) ^ (2 * C2) := one_le_pow₀ (by linarith)
  have h6 : (130000 : ℝ) ≤ (1 / η) ^ 6 := by
    calc (130000 : ℝ) ≤ 10 ^ 6 := by norm_num
      _ ≤ (1 / η) ^ 6 := pow_le_pow_left₀ (by norm_num) hu 6
  calc 2000 * ((G.d : ℝ) + 1) * (1 / η) ≤ 2000 * (65 * (1 / η) ^ (2 * C2)) * (1 / η) := by
        gcongr; linarith
    _ = 130000 * (1 / η) ^ (2 * C2 + 1) := by ring
    _ ≤ _ := mul_pow_le_pow (by linarith) h6 (by omega)

include hV in
lemma wM_le_exp (i : Fin G.d) : (wM G η i : ℝ) ≤ Real.exp (2 * (1 / η) ^ (2 * C3)) := by
  have hu := u_ge_ten hη0 hη1 hG hd
  have h1 := wM_le hη0 hη1 hG hd i
  have hv1 := hG.one_le_norm i
  have hvV := norm_le_vol hG i
  have hP := poly_d_le hη0 hη1 hG hd
  obtain ⟨-, c3, -, -⟩ := gt_consts
  have hpow : (1 / η) ^ (2 * C2 + 7) ≤ (1 / η) ^ (2 * C3) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hA : 1 ≤ 1000 * (G.d + 1) * (1 / η) * ‖G.v i‖ := by
    have : (1 : ℝ) ≤ 1000 * (G.d + 1) * (1 / η) := by
      have : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _
      nlinarith
    nlinarith
  calc (wM G η i : ℝ) ≤ 2000 * (G.d + 1) * (1 / η) * G.vol := by nlinarith
    _ ≤ (1 / η) ^ (2 * C3) * Real.exp ((1 / η) ^ (2 * C3)) := by
        have hv0 : 0 ≤ G.vol := by
          unfold DTorus.vol; exact prod_nonneg fun i _ => norm_nonneg _
        exact mul_le_mul (hP.trans hpow) hV hv0 (pow_nonneg (by linarith) _)
    _ ≤ Real.exp ((1 / η) ^ (2 * C3)) * Real.exp ((1 / η) ^ (2 * C3)) :=
        mul_le_mul_of_nonneg_right (le_exp_self' _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

include hV in
lemma wP_le_exp : wP G η ≤ Real.exp ((1 / η) ^ (2 * C2 + 2 * C3 + 3)) := by
  have hu := u_ge_ten hη0 hη1 hG hd
  have hW := wM_le_exp hη0 hη1 hG hd hV
  set a := 1 + 2 * (1 / η) ^ (2 * C3) with ha
  have hprod : ∏ i, (2 * wM G η i : ℝ) ≤ Real.exp (G.d * a) := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc ∏ i, (2 * wM G η i : ℝ) ≤ ∏ _i : Fin G.d, Real.exp a := by
          refine prod_le_prod (fun i _ => by positivity) fun i _ => ?_
          rw [ha, Real.exp_add]
          exact mul_le_mul h2 (hW i) (by positivity) (by positivity)
      _ = Real.exp a ^ G.d := by rw [prod_const, card_univ, Fintype.card_fin]
      _ = Real.exp (G.d * a) := (Real.exp_nat_mul a G.d).symm
  unfold wP
  have hp0 : 0 ≤ ∏ i, (2 * wM G η i : ℝ) := by positivity
  calc (∏ i, (2 * wM G η i : ℝ)) ^ 3 ≤ Real.exp (G.d * a) ^ 3 := pow_le_pow_left₀ hp0 hprod 3
    _ = Real.exp (3 * (G.d * a)) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ _ := by
        rw [Real.exp_le_exp]
        have h1 : (1 : ℝ) ≤ (1 / η) ^ (2 * C3) := one_le_pow₀ (by linarith)
        have h576 : (576 : ℝ) ≤ (1 / η) ^ 3 := by
          calc (576 : ℝ) ≤ 10 ^ 3 := by norm_num
            _ ≤ (1 / η) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
        have hd0 : (0 : ℝ) ≤ G.d := Nat.cast_nonneg _
        calc 3 * (G.d * a) ≤ 3 * (64 * (1 / η) ^ (2 * C2) * (3 * (1 / η) ^ (2 * C3))) := by
              gcongr; rw [ha]; linarith
          _ = 576 * (1 / η) ^ (2 * C2 + 2 * C3) := by ring
          _ ≤ _ := mul_pow_le_pow (by linarith) h576 (by omega)

include hV in
lemma wδ_ge_exp : Real.exp (-2 * (1 / η) ^ (2 * C2 + 2 * C3 + 3)) ≤ wδ G η := by
  have hu := u_ge_ten hη0 hη1 hG hd
  have hP := wP_le_exp hη0 hη1 hG hd hV
  have hP1 := one_le_wP hG hη0 (by linarith)
  obtain ⟨c2, c3, -, -⟩ := gt_consts
  set Λ := (1 / η) ^ (2 * C2 + 2 * C3 + 3) with hΛ
  have h256 : 256 * (1 / η) ≤ Real.exp Λ := by
    refine le_trans ?_ (le_exp_self' _)
    have : (256 : ℝ) ≤ (1 / η) ^ 3 := by
      calc (256 : ℝ) ≤ 10 ^ 3 := by norm_num
        _ ≤ (1 / η) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    calc 256 * (1 / η) = 256 * (1 / η) ^ 1 := by ring
      _ ≤ _ := mul_pow_le_pow (by linarith) this (by omega)
  unfold wδ
  rw [show -2 * Λ = -(Λ + Λ) by ring, Real.exp_neg, Real.exp_add]
  rw [le_div_iff₀ (by positivity)]
  have e : η = 1 / (1 / η) := by field_simp
  rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  calc 256 * wP G η ≤ (Real.exp Λ / (1 / η)) * Real.exp Λ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith [Real.exp_pos Λ]
    _ = η * (Real.exp Λ * Real.exp Λ) := by rw [e]; field_simp

include hV in
lemma p71δ_ge_exp : Real.exp (-3 * (1 / η) ^ (2 * C2 + 2 * C3 + 3)) ≤ p71δ G η := by
  have hu := u_ge_ten hη0 hη1 hG hd
  have h := wδ_ge_exp hη0 hη1 hG hd hV
  set Λ := (1 / η) ^ (2 * C2 + 2 * C3 + 3) with hΛ
  have hΛ1 : (4 : ℝ) ≤ Λ := by
    have : (1 / η) ≤ Λ := by
      rw [hΛ]; calc (1 / η) = (1 / η) ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  unfold p71δ
  have h4 : 4 ≤ Real.exp Λ := (le_exp_self' Λ).trans' hΛ1
  rw [show -3 * Λ = -2 * Λ + -Λ by ring, Real.exp_add, Real.exp_neg]
  calc Real.exp (-2 * Λ) * (Real.exp Λ)⁻¹ ≤ wδ G η * (1 / 4) := by
        apply mul_le_mul h _ (by positivity) (wδ_pos hG hη0 (by linarith)).le
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; norm_num; linarith
    _ = wδ G η / 4 := by ring

end wbounds

/-! ### Exponential bookkeeping -/

lemma mul_le_exp_add {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hax : a ≤ Real.exp x)
    (hby : b ≤ Real.exp y) : a * b ≤ Real.exp (x + y) := by
  rw [Real.exp_add]; exact mul_le_mul hax hby hb (Real.exp_pos _).le

lemma div_le_exp_add {a b x y : ℝ} (hb : 0 < b) (hax : a ≤ Real.exp x)
    (hby : Real.exp (-y) ≤ b) : a / b ≤ Real.exp (x + y) := by
  rw [div_le_iff₀ hb, Real.exp_add]
  calc a ≤ Real.exp x := hax
    _ = Real.exp x * Real.exp y * Real.exp (-y) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp x * Real.exp y * b := by gcongr

lemma pow_le_exp_mul {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ Real.exp x) (n : ℕ) :
    a ^ n ≤ Real.exp (n * x) := by
  rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ ha hax n

lemma natCast_le_exp (n : ℕ) : (n : ℝ) ≤ Real.exp n := le_exp_self' _

/-! ### The constants of Proposition 4.9 -/

lemma lqK_mul_sq {d : ℕ} (hd : 1 ≤ d) {t ρh : ℝ} (ht0 : 0 < t) (hρh : 0 < ρh) :
    lqK d t ρh * ρh ^ 2 = 20971520000 * 128 ^ (d ^ 2) * (d : ℝ) ^ 6 / t ^ (d ^ 2 + 6) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold lqK lqτ
  have h128 : (128 : ℝ) ^ (d ^ 2) = (2 ^ (d ^ 2)) ^ 2 * 32 ^ (d ^ 2) := by
    rw [← pow_mul, mul_comm (d ^ 2) 2, pow_mul, ← mul_pow]; norm_num
  simp only [div_pow]
  rw [h128, pow_add]
  field_simp
  ring

lemma exp_24_ge : (20971520000 : ℝ) ≤ Real.exp 24 := by
  have h3 : Real.exp 24 = Real.exp 8 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h8 : (2980 : ℝ) ≤ Real.exp 8 := by
    have h2 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_gt_d9
    rw [h2]
    calc (2980 : ℝ) ≤ 2.7182818283 ^ 8 := by norm_num
      _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) this.le 8
  rw [h3]
  calc (20971520000 : ℝ) ≤ 2980 ^ 3 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h8 3

lemma exp_5_ge : (128 : ℝ) ≤ Real.exp 5 := by
  have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.exp_one_gt_d9
  rw [h2]
  calc (128 : ℝ) ≤ 2.7182818283 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) this.le 5

lemma exp_7_ge : (1000 : ℝ) ≤ Real.exp 7 := by
  have h2 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.exp_one_gt_d9
  rw [h2]
  calc (1000 : ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) this.le 7

/-! ### Bounds on the constants of Proposition 7.1 -/

section pbounds

variable {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)} (hSne : S.Nonempty)
  {G : DTorus} (hG : G.Good) (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2))
  (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3)))
  {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
include hη0 hη1 hs

omit [NeZero p] in
lemma card_le_upow : (S.card : ℝ) ≤ (1 / η) ^ (3 * C2 + 2) := by
  have hu := u_ge_ten' hη0 hη1
  have h65 : (65 : ℝ) ≤ (1 / η) ^ 2 := by nlinarith
  exact hs.trans (mul_pow_le_pow (by linarith) h65 le_rfl)

set_option maxHeartbeats 1000000 in
include hSne hG hd hV hρ0 in
lemma K_le : p71K S G η (SLA.eps4 η) ρ * ρ ^ 2 ≤ Real.exp (3 * (1 / η) ^ C4) := by
  have hu := u_ge_ten' hη0 hη1
  obtain ⟨c2, c3, c4, -⟩ := gt_consts
  have hs1 : 1 ≤ S.card := hSne.card_pos
  have hs1' : (1 : ℝ) ≤ S.card := by exact_mod_cast hs1
  have hsu := card_le_upow hη0 hη1 hs
  have hδ := p71δ_ge_exp hη0 hη1 hG hd hV
  have hδ0 := p71δ_pos hG hη0 (by linarith)
  have hwδ := wδ_ge_exp hη0 hη1 hG hd hV
  have hwδ0 := wδ_pos hG hη0 (by linarith)
  set Λ := (1 / η) ^ (2 * C2 + 2 * C3 + 3) with hΛ
  set X := (1 / η) ^ C4 with hX
  set t := p71δ G η ^ 4 with ht
  set n : ℝ := ((S.card : ℕ) : ℝ) with hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have ht0 : 0 < t := by positivity
  have htΛ : Real.exp (-12 * Λ) ≤ t := by
    rw [ht]
    calc Real.exp (-12 * Λ) = Real.exp (-3 * Λ) ^ 4 := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  set ρh := wρh S G η (SLA.eps4 η) ρ with hρh
  have hρh0 : 0 < ρh := by rw [hρh, wρh, SLA.eps4]; positivity
  have hKh := lqK_mul_sq hs1 ht0 hρh0
  -- bound on `K ρh²`
  have hZ1 : lqK S.card t ρh * ρh ^ 2 ≤
      Real.exp (24 + 5 * n ^ 2 + 6 * n + 12 * Λ * (n ^ 2 + 6)) := by
    rw [hKh]
    have h1 : (128 : ℝ) ^ (S.card ^ 2) ≤ Real.exp (5 * n ^ 2) := by
      have := pow_le_exp_mul (by norm_num) exp_5_ge (S.card ^ 2)
      refine this.trans (le_of_eq ?_); congr 1; try (rw [hn]; push_cast; try ring)
    have h2 : (S.card : ℝ) ^ 6 ≤ Real.exp (6 * n) := by
      have := pow_le_exp_mul (by positivity) (natCast_le_exp S.card) 6
      refine this.trans (le_of_eq ?_); congr 1; try (rw [hn]; push_cast; try ring)
    have h3 : Real.exp (-(12 * Λ * (n ^ 2 + 6))) ≤ t ^ (S.card ^ 2 + 6) := by
      have := pow_le_pow_left₀ (Real.exp_pos _).le htΛ (S.card ^ 2 + 6)
      rw [← Real.exp_nat_mul] at this
      refine le_trans (le_of_eq ?_) this
      congr 1; push_cast; rw [hn]; ring
    refine div_le_exp_add (by positivity) ?_ h3
    have := mul_le_exp_add (by positivity) (by positivity)
      (mul_le_exp_add (by norm_num) (by positivity) exp_24_ge h1) h2
    refine this.trans (le_of_eq ?_)
    ring_nf
  -- bound on `ρ / ρh`
  have hZ2 : ρ / ρh ≤ Real.exp (7 + n + 2 * Λ + X) := by
    rw [hρh, wρh, SLA.eps4, ← hX]
    have e : ρ / (wδ G η * Real.exp (-X) * ρ / (1000 * (n + 1))) =
        1000 * (n + 1) / (wδ G η * Real.exp (-X)) := by
      field_simp
    rw [e]
    have hnum : 1000 * (n + 1) ≤ Real.exp (7 + n) := by
      rw [Real.exp_add]
      exact mul_le_mul exp_7_ge (by linarith [Real.add_one_le_exp n]) (by positivity)
        (Real.exp_pos _).le
    have hden : Real.exp (-(2 * Λ + X)) ≤ wδ G η * Real.exp (-X) := by
      rw [neg_add, Real.exp_add]
      exact mul_le_mul (by rw [show -(2 * Λ) = -2 * Λ by ring]; exact hwδ) le_rfl
        (Real.exp_pos _).le hwδ0.le
    exact (div_le_exp_add (by positivity) hnum hden).trans (le_of_eq (by ring_nf))
  have hK : p71K S G η (SLA.eps4 η) ρ * ρ ^ 2 = (lqK S.card t ρh * ρh ^ 2) * (ρ / ρh) ^ 2 := by
    unfold p71K; rw [← ht, ← hρh]; field_simp
  rw [hK]
  have hK0 : 0 ≤ lqK S.card t ρh * ρh ^ 2 := by rw [hKh]; positivity
  have := mul_le_exp_add hK0 (by positivity) hZ1
    (pow_le_exp_mul (by positivity) hZ2 2)
  refine this.trans (Real.exp_le_exp.mpr ?_)
  -- exponent bookkeeping
  set P := (1 / η) ^ (8 * C2 + 2 * C3 + 7) with hP
  have hU2 : n ^ 2 ≤ (1 / η) ^ (6 * C2 + 4) := by
    calc n ^ 2 ≤ ((1 / η) ^ (3 * C2 + 2)) ^ 2 := pow_le_pow_left₀ hn0 hsu 2
      _ = _ := by rw [← pow_mul]; ring_nf
  have hΛ1 : (1 : ℝ) ≤ Λ := one_le_pow₀ (by linarith)
  have hU1 : (1 : ℝ) ≤ (1 / η) ^ (6 * C2 + 4) := one_le_pow₀ (by linarith)
  have hPe : Λ * (1 / η) ^ (6 * C2 + 4) = P := by rw [hΛ, hP, ← pow_add]; congr 1; try omega
  have hnP : n ≤ P := by
    have : n ≤ (1 / η) ^ (6 * C2 + 4) := hsu.trans (pow_le_pow_right₀ (by linarith) (by omega))
    nlinarith
  have hn2P : n ^ 2 ≤ P := by nlinarith
  have hΛP : Λ ≤ P := by nlinarith
  have hΛn2P : Λ * n ^ 2 ≤ P := by rw [← hPe]; exact mul_le_mul_of_nonneg_left hU2 (by linarith)
  have hP1 : 1 ≤ P := by nlinarith
  have hPX : 200 * P ≤ X := by
    have h200 : (200 : ℝ) ≤ (1 / η) ^ 3 := by
      calc (200 : ℝ) ≤ 10 ^ 3 := by norm_num
        _ ≤ (1 / η) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    exact mul_pow_le_pow (by linarith) h200 (by omega)
  have e : 12 * Λ * (n ^ 2 + 6) = 12 * (Λ * n ^ 2) + 72 * Λ := by ring
  push_cast
  linarith

end pbounds

end

end GT
end File_GT_BadDimNum

open Finset KM
open GT in
theorem solution {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)} (hSne : S.Nonempty) {G : DTorus} (hG : G.Good) (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2)) (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) : p71K S G η (SLA.eps4 η) ρ * ρ ^ 2 ≤ Real.exp (3 * (1 / η) ^ C4) :=
  @GT.K_le p _ η hη0 hη1 S hSne G hG hs hd hV ρ hρ0

