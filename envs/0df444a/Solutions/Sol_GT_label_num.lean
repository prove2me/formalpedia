-- Prove2me | solution 1 for GT.label_num
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T11:06:46.386511+00:00
-- url     : https://prove2.me/submissions/53226c1a-0f4b-4f68-8e10-867f66ad9481

import Mathlib
import Definitions.Def_GreenTaoFourCore
import Theorems.Thm_GT_K_le
import Theorems.Thm_GT_R_ge
import Theorems.Thm_GT_label_num_lip

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

lemma wδ_le {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : wδ G η ≤ η / 256 := by
  unfold wδ
  have := one_le_wP hG hη hη1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma p71δ_pos {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : 0 < p71δ G η := by
  unfold p71δ; have := wδ_pos hG hη hη1; positivity

lemma p71δ_le {G : DTorus} (hG : G.Good) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) : p71δ G η ≤ 1 := by
  unfold p71δ; have := wδ_le hG hη hη1; linarith

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

lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp n := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have := pow_le_exp_mul (by norm_num) h2 n
  simpa using this

/-! ### The constants of Proposition 4.9 -/

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

include hSne hG hρ0 in
lemma R_le : p71R S G η (SLA.eps4 η) ρ ≤ SLA.eps4 η * ρ / 1000 := by
  have hs1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hSne.card_pos
  have hδ0 := p71δ_pos hG hη0 (by linarith)
  have hδ1 := p71δ_le hG hη0 (by linarith)
  have hwδ0 := wδ_pos hG hη0 (by linarith)
  have hwδ1 : wδ G η ≤ 1 := (wδ_le hG hη0 (by linarith)).trans (by linarith)
  have heps : 0 < SLA.eps4 η := Real.exp_pos _
  set t := p71δ G η ^ 4 with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ hδ0.le hδ1
  unfold p71R lqR lqτ wρh
  rw [← ht]
  have hD : 1 ≤ 2 ^ (S.card ^ 2) * (S.card : ℝ) * (65536 / t ^ 3 + 1) := by
    have h1 : (1 : ℝ) ≤ 2 ^ (S.card ^ 2) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ 65536 / t ^ 3 + 1 := by
      have : 0 ≤ 65536 / t ^ 3 := by positivity
      linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h1 hs1) h2
  refine (div_le_self (by positivity) hD).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : t * (wδ G η * SLA.eps4 η * ρ / (1000 * (S.card + 1))) ≤
      SLA.eps4 η * ρ / 1000 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : (1000 * ((S.card : ℝ) + 1))⁻¹ ≤ 1000⁻¹ := by
      apply inv_anti₀ (by norm_num); linarith
    have hpos : 0 ≤ SLA.eps4 η * ρ := by positivity
    calc t * (wδ G η * SLA.eps4 η * ρ * (1000 * ((S.card : ℝ) + 1))⁻¹)
        = (t * wδ G η) * (SLA.eps4 η * ρ) * (1000 * ((S.card : ℝ) + 1))⁻¹ := by ring
      _ ≤ 1 * (SLA.eps4 η * ρ) * 1000⁻¹ := by
          gcongr
          nlinarith
      _ = _ := by ring
  have h2 : SLA.eps4 η * ρ ≤ SLA.eps4 η * ρ * (200 * S.card) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  linarith

include hG hd hV in
lemma sum_wM_le : ∑ i, (wM G η i : ℝ) ≤ G.d * Real.exp (2 * (1 / η) ^ (2 * C3)) := by
  calc ∑ i, (wM G η i : ℝ) ≤ ∑ _i : Fin G.d, Real.exp (2 * (1 / η) ^ (2 * C3)) :=
        sum_le_sum fun i _ => wM_le_exp hη0 hη1 hG hd hV i
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

set_option maxHeartbeats 1000000 in
include hSne hG hd hV in
lemma m_le : p71m S G η ≤ Real.exp ((1 / η) ^ C4) := by
  have hu := u_ge_ten' hη0 hη1
  obtain ⟨c2, c3, c4, -⟩ := gt_consts
  have hsu := card_le_upow hη0 hη1 hs
  have hδ := p71δ_ge_exp hη0 hη1 hG hd hV
  have hδ0 := p71δ_pos hG hη0 (by linarith)
  have hsw := sum_wM_le hη0 hη1 hG hs hd hV
  set Λ := (1 / η) ^ (2 * C2 + 2 * C3 + 3) with hΛ
  set n : ℝ := ((S.card : ℕ) : ℝ) with hn
  set D : ℝ := ((G.d : ℕ) : ℝ) with hD
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have h32 : (32 : ℝ) ≤ Real.exp 4 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (32 : ℝ) ≤ 2.7182818283 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) this.le 4
  have hδ4 : Real.exp (-(12 * Λ)) ≤ p71δ G η ^ 4 := by
    calc Real.exp (-(12 * Λ)) = Real.exp (-3 * Λ) ^ 4 := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hδ _
  have h1 : 32 / p71δ G η ^ 4 ≤ Real.exp (4 + 12 * Λ) := div_le_exp_add (by positivity) h32 hδ4
  have h2 := pow_le_exp_mul (by positivity) h1 (S.card ^ 2)
  have h3 : 4 * ∑ i, (wM G η i : ℝ) ≤ Real.exp (4 * D + 2 * (1 / η) ^ (2 * C3)) := by
    rw [Real.exp_add]
    have : 4 * D ≤ Real.exp (4 * D) := le_exp_self' _
    calc 4 * ∑ i, (wM G η i : ℝ) ≤ 4 * (D * Real.exp (2 * (1 / η) ^ (2 * C3))) := by linarith
      _ = (4 * D) * Real.exp (2 * (1 / η) ^ (2 * C3)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  unfold p71m
  refine (mul_le_exp_add (by positivity) (by positivity) h2 h3).trans (Real.exp_le_exp.mpr ?_)
  set P := (1 / η) ^ (8 * C2 + 2 * C3 + 7) with hP
  have hU2 : n ^ 2 ≤ (1 / η) ^ (6 * C2 + 4) := by
    calc n ^ 2 ≤ ((1 / η) ^ (3 * C2 + 2)) ^ 2 := pow_le_pow_left₀ hn0 hsu 2
      _ = _ := by rw [← pow_mul]; ring_nf
  have hΛ1 : (1 : ℝ) ≤ Λ := one_le_pow₀ (by linarith)
  have hU1 : (1 : ℝ) ≤ (1 / η) ^ (6 * C2 + 4) := one_le_pow₀ (by linarith)
  have hPe : Λ * (1 / η) ^ (6 * C2 + 4) = P := by rw [hΛ, hP, ← pow_add]; congr 1; try omega
  have hn2P : n ^ 2 ≤ P := by nlinarith
  have hΛn2P : Λ * n ^ 2 ≤ P := by rw [← hPe]; exact mul_le_mul_of_nonneg_left hU2 (by linarith)
  have hDP : D ≤ P := by
    have h64 : (64 : ℝ) ≤ (1 / η) ^ 2 := by nlinarith
    have := mul_pow_le_pow (by linarith) h64 (a := 2 * C2) (b := 8 * C2 + 2 * C3 + 7) (by omega)
    linarith
  have hC3P : (1 / η) ^ (2 * C3) ≤ P := pow_le_pow_right₀ (by linarith) (by omega)
  have hPX : 1000 * P ≤ (1 / η) ^ C4 := by
    have h1000 : (1000 : ℝ) ≤ (1 / η) ^ 3 := by
      calc (1000 : ℝ) ≤ 10 ^ 3 := by norm_num
        _ ≤ (1 / η) ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    exact mul_pow_le_pow (by linarith) h1000 (by omega)
  have e : ((S.card ^ 2 : ℕ) : ℝ) * (4 + 12 * Λ) = 4 * n ^ 2 + 12 * (Λ * n ^ 2) := by
    rw [hn]; push_cast; ring
  rw [e]
  linarith

include hG hd hV in
lemma emb_le (w : Fin G.d → ℤ) (hw : ∀ i, |(w i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) :
    ‖G.emb (fun i => (w i : ℝ))‖ ≤ Real.exp (5 * G.d + 3 * (1 / η) ^ (2 * C3)) := by
  have hsw := sum_wM_le hη0 hη1 hG hs hd hV
  set D : ℝ := ((G.d : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set W := Real.exp (2 * (1 / η) ^ (2 * C3)) with hW
  have hW1 : 1 ≤ W := by rw [hW, Real.one_le_exp_iff]; positivity
  have hv0 : 0 ≤ G.vol := by unfold DTorus.vol; exact prod_nonneg fun i _ => norm_nonneg _
  have hwi : ∀ i, |(w i : ℝ)| ≤ Real.exp (4 * D) * W := by
    intro i
    refine (hw i).trans ?_
    rw [← mul_sum] at *
    have h4 : 1 + 4 * D ≤ Real.exp (4 * D) := Real.add_one_le_exp _ |>.trans' (by linarith)
    nlinarith
  unfold DTorus.emb
  calc ‖∑ i, (w i : ℝ) • G.v i‖ ≤ ∑ i, ‖(w i : ℝ) • G.v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin G.d, Real.exp (4 * D) * W * G.vol := by
        refine sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hwi i) (norm_le_vol hG i) (norm_nonneg _) (by positivity)
    _ = D * (Real.exp (4 * D) * W * G.vol) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ Real.exp D * (Real.exp (4 * D) * W * Real.exp ((1 / η) ^ (2 * C3))) := by
        gcongr
        exact le_exp_self' _
    _ = _ := by rw [hW, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf

include hG hd in
lemma ratio_le : 2 ^ (G.d ^ 2) * (∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖) ≤
    Real.exp ((1 / η) ^ C3) := by
  have hu := u_ge_ten' hη0 hη1
  obtain ⟨c2, c3, c4, -⟩ := gt_consts
  have hP := poly_d_le hη0 hη1 hG hd
  set D : ℝ := ((G.d : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  set Q := (1 / η) ^ (2 * C2 + 7) with hQ
  have hi : ∀ i, 4 * (wM G η i : ℝ) / ‖G.v i‖ ≤ 4 * Q := by
    intro i
    have hv1 := hG.one_le_norm i
    have h1 := wM_le hη0 hη1 hG hd i
    rw [div_le_iff₀ (by linarith)]
    have : 1000 * (D + 1) * (1 / η) + 1 ≤ Q := by
      have : (1 : ℝ) ≤ 1000 * (D + 1) * (1 / η) := by nlinarith
      linarith
    nlinarith
  have hsum : ∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖ ≤ D * (4 * Q) := by
    calc _ ≤ ∑ _i : Fin G.d, 4 * Q := sum_le_sum fun i _ => hi i
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (2 : ℝ) ^ (G.d ^ 2) ≤ Real.exp (D ^ 2) := by
    have := two_pow_le_exp (G.d ^ 2); rw [hD]; push_cast at this; exact this
  have h3 : D * (4 * Q) ≤ Real.exp (4 * D + Q) := by
    rw [Real.exp_add]
    have := le_exp_self' (4 * D)
    have := le_exp_self' Q
    have hQ0 : 0 ≤ Q := by positivity
    nlinarith [Real.exp_pos (4 * D), Real.exp_pos Q]
  refine (mul_le_exp_add (by positivity) (by positivity) h2 (hsum.trans h3)).trans
    (Real.exp_le_exp.mpr ?_)
  have hD2 : D ^ 2 ≤ 4096 * (1 / η) ^ (4 * C2) := by
    calc D ^ 2 ≤ (64 * (1 / η) ^ (2 * C2)) ^ 2 := pow_le_pow_left₀ hD0 hd 2
      _ = _ := by rw [mul_pow, ← pow_mul]; ring_nf
  have hQ' : Q ≤ (1 / η) ^ (4 * C2 + 7) := pow_le_pow_right₀ (by linarith) (by omega)
  have hD4 : 4 * D ≤ 256 * (1 / η) ^ (4 * C2) := by
    have : (1 / η) ^ (2 * C2) ≤ (1 / η) ^ (4 * C2) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have h7 : (1 / η) ^ (4 * C2) ≤ (1 / η) ^ (4 * C2 + 7) := pow_le_pow_right₀ (by linarith) (by omega)
  have h5000 : (5000 : ℝ) ≤ (1 / η) ^ 4 := by
    calc (5000 : ℝ) ≤ 10 ^ 4 := by norm_num
      _ ≤ (1 / η) ^ 4 := pow_le_pow_left₀ (by norm_num) hu 4
  have := mul_pow_le_pow (by linarith) h5000 (a := 4 * C2 + 7) (b := C3) (by omega)
  linarith

end pbounds

set_option maxHeartbeats 8000000 in
/-- The numerical facts about one poorly distributed label. -/
theorem label_num {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)}
    (hSne : S.Nonempty) {G : DTorus} (hG : G.Good)
    (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    100 * S.card * SLA.eps4 η ≤ wδ G η / 2 ∧
    0 < p71R S G η (SLA.eps4 η) ρ ∧ 4 * p71R S G η (SLA.eps4 η) ρ ≤ ρ / 2 ∧
    0 < ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ≤ 1 ∧
    Real.exp (-(1 / η) ^ C5) * ρ ≤ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧
    2 ^ (G.d ^ 2) * (∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖) ≤ Real.exp ((1 / η) ^ C3) ∧
    p71m S G η ≤ Real.exp ((1 / η) ^ C4) ∧
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ p71m S G η → ∀ w : Fin G.d → ℤ,
      (∀ i, |(w i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) →
      4 * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) ≤ p71R S G η (SLA.eps4 η) ρ ∧
      50 * S.card * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) / p71R S G η (SLA.eps4 η) ρ +
        50 * S.card * p71R S G η (SLA.eps4 η) ρ / (ρ / 2) ≤ η ^ C3 / 4 ∧
      p71L S G η (SLA.eps4 η) ρ m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)) / 2) *
        ‖G.emb (fun i => (w i : ℝ))‖ ≤ η ^ C3 / 4 := by
  have hlip := label_num_lip hη0 hη1 hSne hG hs hd hV hρ0 hρ1
  have hu := u_ge_ten' hη0 hη1
  obtain ⟨c2, c3, c4, c5⟩ := gt_consts
  have hsu := card_le_upow hη0 hη1 hs
  have hRge := R_ge (hη0 := hη0) (hη1 := hη1) (hSne := hSne) (hG := hG) (hs := hs) (hd := hd)
    (hV := hV) (hρ0 := hρ0)
  have hRle := R_le (hη0 := hη0) (hη1 := hη1) (hSne := hSne) (hG := hG) (hs := hs) (hρ0 := hρ0)
  have hKle := K_le (hη0 := hη0) (hη1 := hη1) (hSne := hSne) (hG := hG) (hs := hs) (hd := hd)
    (hV := hV) (hρ0 := hρ0)
  have hmle := m_le (hη0 := hη0) (hη1 := hη1) (hSne := hSne) (hG := hG) (hs := hs) (hd := hd)
    (hV := hV)
  have hwδ := wδ_ge_exp hη0 hη1 hG hd hV
  have hrat := ratio_le (hη0 := hη0) (hη1 := hη1) (hG := hG) (hs := hs) (hd := hd)
  have hembf := fun w hw => emb_le (hη0 := hη0) (hη1 := hη1) (hG := hG) (hs := hs) (hd := hd)
    (hV := hV) w hw
  have hηC3 : η ^ C3 = 1 / (1 / η) ^ C3 := by rw [one_div_pow, one_div_one_div]
  rw [hηC3] at hlip ⊢
  have hepsdef : SLA.eps4 η = Real.exp (-(1 / η) ^ C4) := rfl
  rw [hepsdef] at hRle hRge hKle hlip ⊢
  clear c2
  generalize C5 = D5 at *
  generalize C4 = D4 at *
  generalize C3 = D3 at *
  generalize C2 = D2 at *
  set u := 1 / η with hu_def
  have hu1 : (1 : ℝ) ≤ u := by linarith
  set X := u ^ D4 with hX
  set R := p71R S G η (Real.exp (-X)) ρ with hR_def
  have hX2 : u ^ (2 * D4) = X ^ 2 := by rw [hX, ← pow_mul]; ring_nf
  rw [hX2] at hlip ⊢
  have hX10 : 10 ≤ X := by
    calc (10 : ℝ) ≤ u := hu
      _ = u ^ 1 := (pow_one u).symm
      _ ≤ X := pow_le_pow_right₀ hu1 (by omega)
  -- generic growth: `c * u^a ≤ X` for small `a`
  have hgrow : ∀ a : ℕ, a + 10 ≤ D4 → 1000 * u ^ a ≤ X := by
    intro a ha
    have h1000 : (1000 : ℝ) ≤ u ^ 3 := by
      calc (1000 : ℝ) = 10 ^ 3 := by norm_num
        _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
    exact mul_pow_le_pow hu1 h1000 (by omega)
  have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have heX : Real.exp (-X) ≤ 1 / 10 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp X; norm_num; linarith
  have hRρ : R ≤ ρ / 10000 := by
    calc R ≤ Real.exp (-X) * ρ / 1000 := hRle
      _ ≤ (1 / 10) * ρ / 1000 := by gcongr
      _ = ρ / 10000 := by ring
  have hX2X : 10 * X ≤ X ^ 2 := by nlinarith
  -- `1/R ≤ exp(2X)/ρ`
  have hRinv : 1 / R ≤ Real.exp (2 * X) / ρ := by
    rw [div_le_div_iff₀ hR0 hρ0]
    have : ρ * Real.exp (-2 * X) * Real.exp (2 * X) = ρ := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have h2 := mul_le_mul_of_nonneg_right hRge (Real.exp_pos (2 * X)).le
    nlinarith
  have hwd0 : 0 < wδ G η := lt_of_lt_of_le (Real.exp_pos _) hwδ
  refine ⟨?_, hR0, by linarith, by positivity, ?_, ?_, hrat, hmle, ?_⟩
  · -- `100 |S| ε ≤ wδ/2`
    set a := 2 * D2 + 2 * D3 + 3
    have hSa : 200 * (S.card : ℝ) ≤ u ^ a := by
      have h200 : (200 : ℝ) ≤ u ^ 3 := by
        calc (200 : ℝ) ≤ 10 ^ 3 := by norm_num
          _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
      have := mul_pow_le_pow hu1 h200 (a := 3 * D2 + 2) (b := a) (by omega)
      nlinarith
    have hua : 1000 * u ^ a ≤ X := hgrow a (by omega)
    have hua0 : 0 ≤ u ^ a := by positivity
    calc 100 * (S.card : ℝ) * Real.exp (-X) ≤ u ^ a / 2 * Real.exp (-X) := by
          gcongr; linarith
      _ ≤ Real.exp (u ^ a) / 2 * Real.exp (-X) := by
          gcongr; exact le_exp_self' _
      _ = Real.exp (u ^ a - X) / 2 := by rw [div_mul_eq_mul_div, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-2 * u ^ a) / 2 := by gcongr; linarith
      _ ≤ wδ G η / 2 := by gcongr
  · calc ρ * Real.exp (-X ^ 2) ≤ 1 * 1 := by
          gcongr
          rw [Real.exp_le_one_iff]; nlinarith
      _ = 1 := by ring
  · have : X ^ 2 ≤ u ^ D5 := by
      rw [← hX2]; exact pow_le_pow_right₀ hu1 (by omega)
    rw [mul_comm]
    gcongr
  · intro m hm1 hmb w hw
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hmX : (m : ℝ) ≤ Real.exp X := hmb.trans hmle
    have hτ0 : 0 < ρ * Real.exp (-X ^ 2) := by positivity
    -- `m τ ≤ ρ exp(-3X) exp(-X)`-type bound
    have hmτ : (m : ℝ) * (ρ * Real.exp (-X ^ 2)) ≤ ρ * Real.exp (-3 * X) * Real.exp (-X) := by
      calc (m : ℝ) * (ρ * Real.exp (-X ^ 2)) ≤ Real.exp X * (ρ * Real.exp (-X ^ 2)) := by
            gcongr
        _ = ρ * Real.exp (X + -X ^ 2) := by rw [Real.exp_add]; ring
        _ ≤ ρ * Real.exp (-3 * X + -X) := by
            have h' : X + -X ^ 2 ≤ -3 * X + -X := by linarith
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h') hρ0.le
        _ = _ := by rw [Real.exp_add]; ring
    have he3 : Real.exp (-3 * X) ≤ Real.exp (-2 * X) := by gcongr; linarith
    have hμ : (m : ℝ) * (ρ * Real.exp (-X ^ 2)) / R ≤ Real.exp (-X) := by
      rw [div_le_iff₀ hR0]
      calc (m : ℝ) * (ρ * Real.exp (-X ^ 2)) ≤ ρ * Real.exp (-3 * X) * Real.exp (-X) := hmτ
        _ ≤ ρ * Real.exp (-2 * X) * Real.exp (-X) := by gcongr
        _ ≤ R * Real.exp (-X) := by gcongr
        _ = _ := by ring
    have hS3 : 400 * (S.card : ℝ) * u ^ D3 * 2 ≤ Real.exp X := by
      have h800 : (800 : ℝ) ≤ u ^ 3 := by
        calc (800 : ℝ) ≤ 10 ^ 3 := by norm_num
          _ ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu 3
      have e1 : (S.card : ℝ) * u ^ D3 ≤ u ^ (3 * D2 + 2 + D3) := by
        rw [pow_add]; gcongr
      have e2 := mul_pow_le_pow hu1 h800 (a := 3 * D2 + 2 + D3) (b := 3 * D2 + D3 + 5) (by omega)
      have e3 : u ^ (3 * D2 + D3 + 5) ≤ X := pow_le_pow_right₀ hu1 (by omega)
      have e4 := le_exp_self' X
      nlinarith
    have huC3 : 0 < u ^ D3 := by positivity
    refine ⟨?_, ?_, ?_⟩
    · calc 4 * ((m : ℝ) * (ρ * Real.exp (-X ^ 2))) ≤ 4 * (ρ * Real.exp (-3 * X) * Real.exp (-X)) := by
            gcongr
        _ ≤ 4 * (ρ * Real.exp (-2 * X) * (1 / 10)) := by gcongr
        _ ≤ ρ * Real.exp (-2 * X) := by nlinarith [Real.exp_pos (-2 * X)]
        _ ≤ R := hRge
    · have h2 : R / (ρ / 2) ≤ Real.exp (-X) := by
        rw [div_le_iff₀ (by positivity)]
        calc R ≤ Real.exp (-X) * ρ / 1000 := hRle
          _ ≤ Real.exp (-X) * (ρ / 2) := by nlinarith [Real.exp_pos (-X)]
      have e1 : 50 * S.card * (m * (ρ * Real.exp (-X ^ 2))) / R +
          50 * S.card * R / (ρ / 2) ≤ 100 * S.card * Real.exp (-X) := by
        have e0 : 50 * S.card * (m * (ρ * Real.exp (-X ^ 2))) / R + 50 * S.card * R / (ρ / 2) =
            50 * S.card * (m * (ρ * Real.exp (-X ^ 2)) / R) + 50 * S.card * (R / (ρ / 2)) := by
          ring
        rw [e0]
        have t1 := mul_le_mul_of_nonneg_left hμ (by positivity : (0 : ℝ) ≤ 50 * S.card)
        have t2 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 50 * S.card)
        linarith
      refine e1.trans ?_
      rw [div_div, le_div_iff₀ (by positivity)]
      calc 100 * (S.card : ℝ) * Real.exp (-X) * (u ^ D3 * 4)
          = (400 * S.card * u ^ D3) * Real.exp (-X) := by ring
        _ ≤ (Real.exp X / 2) * Real.exp (-X) := by gcongr; linarith
        _ = 1 / 2 := by rw [div_mul_eq_mul_div, ← Real.exp_add]; simp
        _ ≤ 1 := by norm_num
    · exact hlip m hm1 hmb w hw

end

end GT
end File_GT_BadDimNum

open Finset KM
open GT in
theorem solution {p : ℕ} [NeZero p] {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 10) {S : Finset (ZMod p)}
    (hSne : S.Nonempty) {G : DTorus} (hG : G.Good)
    (hs : (S.card : ℝ) ≤ 65 * (1 / η) ^ (3 * C2)) (hd : (G.d : ℝ) ≤ 64 * (1 / η) ^ (2 * C2))
    (hV : G.vol ≤ Real.exp ((1 / η) ^ (2 * C3))) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    100 * S.card * SLA.eps4 η ≤ wδ G η / 2 ∧
    0 < p71R S G η (SLA.eps4 η) ρ ∧ 4 * p71R S G η (SLA.eps4 η) ρ ≤ ρ / 2 ∧
    0 < ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ≤ 1 ∧
    Real.exp (-(1 / η) ^ C5) * ρ ≤ ρ * Real.exp (-(1 / η) ^ (2 * C4)) ∧
    2 ^ (G.d ^ 2) * (∑ i, 4 * (wM G η i : ℝ) / ‖G.v i‖) ≤ Real.exp ((1 / η) ^ C3) ∧
    p71m S G η ≤ Real.exp ((1 / η) ^ C4) ∧
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ p71m S G η → ∀ w : Fin G.d → ℤ,
      (∀ i, |(w i : ℝ)| ≤ 1 + ∑ j, 4 * (wM G η j : ℝ)) →
      4 * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) ≤ p71R S G η (SLA.eps4 η) ρ ∧
      50 * S.card * (m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)))) / p71R S G η (SLA.eps4 η) ρ +
        50 * S.card * p71R S G η (SLA.eps4 η) ρ / (ρ / 2) ≤ η ^ C3 / 4 ∧
      p71L S G η (SLA.eps4 η) ρ m * (ρ * Real.exp (-(1 / η) ^ (2 * C4)) / 2) *
        ‖G.emb (fun i => (w i : ℝ))‖ ≤ η ^ C3 / 4 :=
  @GT.label_num p _ η hη0 hη1 S hSne G hG hs hd hV ρ hρ0 hρ1

