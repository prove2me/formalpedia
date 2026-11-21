-- Prove2me | solution 1 for FasterPrimeEnum.lemma_2_11
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T15:20:49.191835+00:00
-- url     : https://prove2.me/submissions/69daaf6e-4e2a-4dd4-bfb6-01ebb890f0b4

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace FasterPrimeEnum

open Zsqrtd Module

noncomputable section

/-- The `ℤ`-basis `{1, √d}` of `ℤ√d`. -/
def zbasis (d : ℤ) : Basis (Fin 2) ℤ (ℤ√d) :=
  Basis.ofEquivFun
    { toFun := fun x => ![x.re, x.im]
      invFun := fun f => ⟨f 0, f 1⟩
      left_inv := by intro x; ext <;> simp
      right_inv := by intro f; ext i; fin_cases i <;> simp
      map_add' := by intro x y; ext i; fin_cases i <;> simp
      map_smul' := by intro a x; ext i; fin_cases i <;> simp }

@[simp] lemma zbasis_repr_apply (d : ℤ) (x : ℤ√d) (i : Fin 2) :
    (zbasis d).repr x i = ![x.re, x.im] i := by
  simp [zbasis]

lemma zbasis_zero (d : ℤ) : zbasis d 0 = (1 : ℤ√d) := by
  simp [zbasis, Basis.coe_ofEquivFun, Zsqrtd.ext_iff]

lemma zbasis_one (d : ℤ) : zbasis d 1 = (Zsqrtd.sqrtd : ℤ√d) := by
  simp [zbasis, Basis.coe_ofEquivFun, Zsqrtd.ext_iff]

lemma det_zbasis_mul (d : ℤ) (θ : ℤ√d) :
    (zbasis d).det (fun i => θ * zbasis d i) = Zsqrtd.norm θ := by
  rw [Basis.det_apply]
  have hmat : (zbasis d).toMatrix (fun i => θ * zbasis d i)
      = !![θ.re, d * θ.im; θ.im, θ.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Basis.toMatrix_apply, zbasis_repr_apply, zbasis_zero, zbasis_one]
  rw [hmat, Matrix.det_fin_two]
  simp [Zsqrtd.norm]

/-- The cardinality of `ℤ√d ⧸ (θ)` equals `|norm θ|`, for `θ ≠ 0`. -/
lemma natCard_quot_span (d : ℤ) [IsDomain (ℤ√d)] (θ : ℤ√d) (hθ : θ ≠ 0) :
    Nat.card (ℤ√d ⧸ Ideal.span {θ}) = (Zsqrtd.norm θ).natAbs := by
  have h := AddSubgroup.index_eq_natAbs_det (zbasis d) (Ideal.span {θ}).toAddSubgroup
    (Ideal.basisSpanSingleton (zbasis d) hθ)
  have hcard : Nat.card (ℤ√d ⧸ Ideal.span {θ}) = (Ideal.span {θ}).toAddSubgroup.index := rfl
  rw [hcard, h]
  congr 1
  change (zbasis d).det (fun i => θ * zbasis d i) = Zsqrtd.norm θ
  exact det_zbasis_mul d θ

/-! ## The ring `ℤ√(-2)` -/

instance instNoZeroDivisorsSqrtNegTwo : NoZeroDivisors (ℤ√(-2)) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b hab
    have h : Zsqrtd.norm (a * b) = 0 := by rw [hab]; exact Zsqrtd.norm_zero
    rw [Zsqrtd.norm_mul] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl ((Zsqrtd.norm_eq_zero_iff (d := -2) (by norm_num) a).mp h')
    · exact Or.inr ((Zsqrtd.norm_eq_zero_iff (d := -2) (by norm_num) b).mp h')

instance instIsDomainSqrtNegTwo : IsDomain (ℤ√(-2)) := NoZeroDivisors.to_isDomain _

lemma norm_mk_negTwo (a b : ℤ) : (⟨a, b⟩ : ℤ√(-2)).norm = a ^ 2 + 2 * b ^ 2 := by
  rw [Zsqrtd.norm_def]
  ring

lemma norm_nonneg_negTwo (x : ℤ√(-2)) : 0 ≤ Zsqrtd.norm x :=
  Zsqrtd.norm_nonneg (d := -2) (by norm_num) x

lemma zmod2_sq (x : ZMod 2) : x ^ 2 = x := by
  have h : x = 0 ∨ x = 1 := by revert x; decide
  rcases h with rfl | rfl <;> decide

lemma zmod2_nat_odd (n : ℕ) (hn : n % 2 = 1) : (n : ZMod 2) = 1 := by
  have h : (n : ZMod 2) = ((1 : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_eq_natCast_iff']
    simpa using hn
  simpa using h

/-- Euclidean division for `ℤ√(-2)`: the remainder has strictly smaller norm. -/
lemma exists_div_lt (z w : ℤ√(-2)) (hw : w ≠ 0) :
    ∃ q : ℤ√(-2), Zsqrtd.norm (z - q * w) < Zsqrtd.norm w := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, e⟩ := w
  have hw' : ¬(c = 0 ∧ e = 0) := by
    intro h
    apply hw
    ext <;> simp [h.1, h.2]
  set N : ℤ := c ^ 2 + 2 * e ^ 2 with hN
  have hNpos : 0 < N := by
    rcases not_and_or.mp hw' with h | h
    · have hc : 0 < c ^ 2 := by
        have hc0 : c ≠ 0 := h
        simpa [pow_two] using (mul_self_pos (a := c)).mpr hc0
      nlinarith
    · have he : 0 < e ^ 2 := by
        simpa [pow_two] using (mul_self_pos (a := e)).mpr h
      nlinarith
  set A : ℤ := a * c + 2 * b * e with hA
  set B : ℤ := b * c - a * e with hB
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  have hNqne : (N : ℚ) ≠ 0 := ne_of_gt hNq
  set u : ℚ := (A : ℚ) / (N : ℚ) with hu
  set v : ℚ := (B : ℚ) / (N : ℚ) with hv
  set p : ℤ := round u with hp
  set m : ℤ := round v with hm
  refine ⟨(⟨p, m⟩ : ℤ√(-2)), ?_⟩
  show Zsqrtd.norm ((⟨a, b⟩ : ℤ√(-2)) - (⟨p, m⟩ : ℤ√(-2)) * (⟨c, e⟩ : ℤ√(-2))) <
    Zsqrtd.norm (⟨c, e⟩ : ℤ√(-2))
  set α : ℤ := a - p * c + 2 * m * e with hαdef
  set β : ℤ := b - p * e - m * c with hβdef
  have hα : (α : ℚ) = c * (u - p) - 2 * e * (v - m) := by
    simp only [hαdef, hu, hv, hA, hB]
    field_simp [hNqne]
    rw [hN]
    push_cast
    ring
  have hβ : (β : ℚ) = e * (u - p) + c * (v - m) := by
    simp only [hβdef, hu, hv, hA, hB]
    field_simp [hNqne]
    rw [hN]
    push_cast
    ring
  have hkey : (α : ℚ) ^ 2 + 2 * (β : ℚ) ^ 2 =
      (N : ℚ) * ((u - p) ^ 2 + 2 * (v - m) ^ 2) := by
    rw [hα, hβ]
    rw [hN]
    push_cast
    ring
  have hp2 : |u - p| ≤ 1 / 2 := by
    have h := abs_sub_round u
    simpa [hp] using h
  have hm2 : |v - m| ≤ 1 / 2 := by
    have h := abs_sub_round v
    simpa [hm] using h
  have h1 : (u - p) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg (u - p)) hp2 2
    norm_num at h ⊢
    exact h
  have h2 : (v - m) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    have h := pow_le_pow_left₀ (abs_nonneg (v - m)) hm2 2
    norm_num at h ⊢
    exact h
  have hlt : (α : ℚ) ^ 2 + 2 * (β : ℚ) ^ 2 < (N : ℚ) := by
    rw [hkey]
    nlinarith
  have hfin : α ^ 2 + 2 * β ^ 2 < N := by
    have hcast : ((α ^ 2 + 2 * β ^ 2 : ℤ) : ℚ) < (N : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hnorm : Zsqrtd.norm ((⟨a, b⟩ : ℤ√(-2)) - (⟨p, m⟩ : ℤ√(-2)) * (⟨c, e⟩ : ℤ√(-2))) =
      α ^ 2 + 2 * β ^ 2 := by
    rw [hαdef, hβdef]
    simp [Zsqrtd.norm_def]
    ring
  rw [hnorm]
  have hwN : Zsqrtd.norm (⟨c, e⟩ : ℤ√(-2)) = N := by
    rw [norm_mk_negTwo, hN]
  rw [hwN]
  exact hfin

/-- Every ideal of `ℤ√(-2)` is principal. -/
lemma isPrincipal_ideal (I : Ideal (ℤ√(-2))) : I.IsPrincipal := by
  classical
  by_cases hI : I = ⊥
  · rw [hI]
    exact bot_isPrincipal
  · have hne : ∃ x ∈ I, x ≠ 0 := by
      by_contra h
      apply hI
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      exact h ⟨x, hx, hx0⟩
    obtain ⟨x0, hx0I, hx0ne⟩ := hne
    let S : ℕ → Prop := fun k => ∃ x ∈ I, x ≠ 0 ∧ (Zsqrtd.norm x).natAbs = k
    have hS : ∃ k, S k := ⟨_, x0, hx0I, hx0ne, rfl⟩
    obtain ⟨θ, hθI, hθne, hθnorm⟩ := Nat.find_spec hS
    have hmin : ∀ y ∈ I, y ≠ 0 → (Zsqrtd.norm θ).natAbs ≤ (Zsqrtd.norm y).natAbs := by
      intro y hy hyne
      have h := Nat.find_min' hS (show S (Zsqrtd.norm y).natAbs from ⟨y, hy, hyne, rfl⟩)
      omega
    refine ⟨θ, ?_⟩
    apply _root_.le_antisymm
    · intro x hx
      obtain ⟨q, hq⟩ := exists_div_lt x θ hθne
      set r : ℤ√(-2) := x - q * θ with hr
      have hrI : r ∈ I := by
        rw [hr]
        exact I.sub_mem hx (I.mul_mem_left q hθI)
      by_cases hr0 : r = 0
      · have hxq : x = q * θ := by
          rw [hr] at hr0
          exact sub_eq_zero.mp hr0
        rw [Ideal.mem_span_singleton]
        exact ⟨q, by rw [hxq, mul_comm]⟩
      · exfalso
        have h1 := hmin r hrI hr0
        have h2 : (Zsqrtd.norm r).natAbs < (Zsqrtd.norm θ).natAbs := by
          have hq' := hq
          rw [hr] at hq'
          have hrnn := norm_nonneg_negTwo r
          have htnn := norm_nonneg_negTwo θ
          have h1 : ((Zsqrtd.norm r).natAbs : ℤ) = Zsqrtd.norm r := Int.natAbs_of_nonneg hrnn
          have h2 : ((Zsqrtd.norm θ).natAbs : ℤ) = Zsqrtd.norm θ := Int.natAbs_of_nonneg htnn
          omega
        omega
    · rw [Ideal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hθI

/-- The units of `ℤ√(-2)` are `±1`. -/
lemma unit_cases_negTwo (u : ℤ√(-2)) (hu : Zsqrtd.norm u = 1) :
    u = 1 ∨ u = -1 := by
  have h : u.re ^ 2 + 2 * u.im ^ 2 = 1 := by
    have hh := hu
    rw [Zsqrtd.norm_def] at hh
    nlinarith
  have him0 : u.im = 0 := by
    have h2 : u.im ^ 2 = 0 := by nlinarith [sq_nonneg u.im]
    exact mul_self_eq_zero.mp (by simpa [pow_two] using h2)
  have hre : u.re ^ 2 = 1 := by nlinarith
  have hre1 : u.re = 1 ∨ u.re = -1 := by
    have h1 : -1 ≤ u.re := by nlinarith
    have h2 : u.re ≤ 1 := by nlinarith
    have h3 : u.re = -1 ∨ u.re = 0 ∨ u.re = 1 := by omega
    rcases h3 with hh | hh | hh
    · exact Or.inr hh
    · rw [hh] at hre; norm_num at hre
    · exact Or.inl hh
  have hu_eq : u = ⟨u.re, u.im⟩ := by cases u; rfl
  rcases hre1 with hh | hh
  · left; rw [hu_eq, hh, him0]; rfl
  · right; rw [hu_eq, hh, him0]; rfl

end

end FasterPrimeEnum

open FasterPrimeEnum Zsqrtd Module

theorem solution (n : ℕ) (hn : n % 2 = 1) :
    Set.BijOn (fun ab : ℤ × ℤ => Ideal.span {(⟨ab.1, ab.2⟩ : ℤ√(-2))})
      {ab : ℤ × ℤ | ab.1 ^ 2 + 2 * ab.2 ^ 2 = (n : ℤ) ∧ 1 ≤ ab.1}
      {I : Ideal (ℤ√(-2)) | Nat.card (ℤ√(-2) ⧸ I) = n} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hne : (⟨a, b⟩ : ℤ√(-2)) ≠ 0 := by
      intro h
      have ha : a = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hnorm : (⟨a, b⟩ : ℤ√(-2)).norm = (n : ℤ) := by
      rw [norm_mk_negTwo]
      exact h1
    have hstep : Nat.card (ℤ√(-2) ⧸ Ideal.span {(⟨a, b⟩ : ℤ√(-2))}) =
        (Zsqrtd.norm (⟨a, b⟩ : ℤ√(-2))).natAbs := natCard_quot_span (-2) _ hne
    change Nat.card (ℤ√(-2) ⧸ Ideal.span {(⟨a, b⟩ : ℤ√(-2))}) = n
    rw [hstep, hnorm, Int.natAbs_natCast]
  · rintro ⟨a, b⟩ ⟨h1, h2⟩ ⟨a', b'⟩ ⟨h1', h2'⟩ heq
    simp only at h1 h2 h1' h2'
    have heq' : Ideal.span {(⟨a, b⟩ : ℤ√(-2))} = Ideal.span {(⟨a', b'⟩ : ℤ√(-2))} := heq
    have hn1 : (⟨a, b⟩ : ℤ√(-2)).norm = (n : ℤ) := by rw [norm_mk_negTwo]; exact h1
    have hn1' : (⟨a', b'⟩ : ℤ√(-2)).norm = (n : ℤ) := by rw [norm_mk_negTwo]; exact h1'
    have hne : (⟨a, b⟩ : ℤ√(-2)) ≠ 0 := by
      intro h
      have ha : a = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hne' : (⟨a', b'⟩ : ℤ√(-2)) ≠ 0 := by
      intro h
      have ha : a' = 0 := by simpa using congrArg Zsqrtd.re h
      omega
    have hassoc : Associated (⟨a, b⟩ : ℤ√(-2)) (⟨a', b'⟩ : ℤ√(-2)) :=
      Ideal.span_singleton_eq_span_singleton.mp heq'
    obtain ⟨u, hu⟩ := hassoc
    have hnu : Zsqrtd.norm (u : ℤ√(-2)) = 1 := by
      have h := congrArg Zsqrtd.norm hu
      rw [Zsqrtd.norm_mul, hn1, hn1'] at h
      have hnz : (n : ℤ) ≠ 0 := by omega
      have h2' : (n : ℤ) * Zsqrtd.norm (u : ℤ√(-2)) = (n : ℤ) * 1 := by simpa using h
      simpa using mul_left_cancel₀ hnz h2'
    rcases unit_cases_negTwo (u : ℤ√(-2)) hnu with hu1 | hu1
    · rw [hu1] at hu
      simp only [mul_one, Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im] at hu
      obtain ⟨hre, him⟩ := hu
      subst hre
      subst him
      rfl
    · rw [hu1] at hu
      simp only [Zsqrtd.ext_iff, Zsqrtd.re, Zsqrtd.im, Zsqrtd.re_mul, Zsqrtd.im_mul,
        Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_one, Zsqrtd.im_one, mul_neg, mul_one,
        add_zero, zero_mul, neg_mul] at hu
      obtain ⟨hre, him⟩ := hu
      omega
  · intro I hI
    haveI : I.IsPrincipal := isPrincipal_ideal I
    let θ : ℤ√(-2) := Submodule.IsPrincipal.generator I
    have hspan : Ideal.span {θ} = I := Ideal.span_singleton_generator I
    have hcard : Nat.card (ℤ√(-2) ⧸ Ideal.span {θ}) = n := by rw [hspan]; exact hI
    have hθne : θ ≠ 0 := by
      intro h0
      have h2 : Nat.card (ℤ√(-2) ⧸ Ideal.span {(0 : ℤ√(-2))}) = n := by
        rw [← h0]; exact hcard
      rw [Set.singleton_zero, Ideal.span_zero] at h2
      have h3 : Nat.card (ℤ√(-2) ⧸ (⊥ : Ideal (ℤ√(-2)))) = 0 := by
        rw [← Submodule.cardQuot_apply]
        exact Submodule.cardQuot_bot ℤ (ℤ√(-2))
      rw [h3] at h2
      omega
    have hnormabs : (Zsqrtd.norm θ).natAbs = n := by
      rw [← natCard_quot_span (-2) θ hθne]
      exact hcard
    have hnorm : Zsqrtd.norm θ = (n : ℤ) := by
      have hnn : 0 ≤ Zsqrtd.norm θ := norm_nonneg_negTwo θ
      have hcast : ((Zsqrtd.norm θ).natAbs : ℤ) = Zsqrtd.norm θ := Int.natAbs_of_nonneg hnn
      rw [hnormabs] at hcast
      exact hcast.symm
    set a := θ.re with ha
    set c := θ.im with hc
    have hθ_eq : θ = ⟨a, c⟩ := by ext <;> simp [ha, hc]
    have hsq : a ^ 2 + 2 * c ^ 2 = (n : ℤ) := by
      have hh := hnorm
      rw [hθ_eq, norm_mk_negTwo] at hh
      exact hh
    have han0 : a ≠ 0 := by
      intro h0
      have hdvd : (2 : ℤ) ∣ (n : ℤ) := by
        refine ⟨c ^ 2, ?_⟩
        rw [h0] at hsq
        linarith
      have hn2 : (n : ZMod 2) = 1 := zmod2_nat_odd n hn
      have hzero : (n : ZMod 2) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) 2).mpr hdvd
      rw [hn2] at hzero
      exact absurd hzero (by decide)
    rcases lt_or_gt_of_ne han0 with ha_neg | ha_pos
    · refine ⟨(-a, -c), ⟨?_, ?_⟩, ?_⟩
      · nlinarith [hsq]
      · omega
      · change Ideal.span {(⟨-a, -c⟩ : ℤ√(-2))} = I
        have h1 : (⟨-a, -c⟩ : ℤ√(-2)) = -θ := by
          rw [hθ_eq]
          ext <;> simp
        rw [h1, Ideal.span_singleton_neg, hspan]
    · refine ⟨(a, c), ⟨?_, ?_⟩, ?_⟩
      · exact hsq
      · omega
      · change Ideal.span {(⟨a, c⟩ : ℤ√(-2))} = I
        rw [← hθ_eq, hspan]
