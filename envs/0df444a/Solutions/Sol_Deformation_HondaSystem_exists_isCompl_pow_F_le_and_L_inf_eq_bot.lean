-- Prove2me | solution 1 for Deformation.HondaSystem.exists_isCompl_pow_F_le_and_L_inf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/927196a0-59d0-5f7d-8480-7e5b1c45ea3c

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u

namespace Deformation
p2m_export "Deformation" "HondaSystem"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "sh1_le sh2' sh1_ge L"
namespace SplitM
p2m_open "Deformation.HondaSystem Deformation"

open LinearMap

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {r : ℕ}

local notation "E" r => Module.End 𝓞 (Fin r → 𝓞)

theorem O_cancel (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} (h : (p : 𝓞) * a = 0) : a = 0 := by
  exact (mem_nonZeroDivisors_iff.mp hp).1 a h

theorem vec_cancel (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {x y : Fin r → 𝓞}
    (h : (p : 𝓞) • x = (p : 𝓞) • y) : x = y := by
  have h0 : (p : 𝓞) • (x - y) = 0 := by rw [smul_sub, h, sub_self]
  have : x - y = 0 := funext fun i => O_cancel p hp (by simpa using congrFun h0 i)
  exact sub_eq_zero.mp this

theorem endo_cancel (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {S T : Module.End 𝓞 (Fin r → 𝓞)}
    (h : (p : 𝓞) • S = (p : 𝓞) • T) : S = T := by
  refine LinearMap.ext fun m => ?_
  exact vec_cancel p hp (by simpa using LinearMap.congr_fun h m)

section complete

theorem O_haus [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {x : 𝓞} (h : ∀ k : ℕ, (p : 𝓞) ^ k ∣ x) : x = 0 := by
  have hH : IsHausdorff (Ideal.span {(p : 𝓞)}) 𝓞 := inferInstance
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact h n

theorem vec_haus [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {x : Fin r → 𝓞} (h : ∀ k : ℕ, ∃ y : Fin r → 𝓞, x = (p : 𝓞) ^ k • y) : x = 0 := by
  funext i
  refine O_haus p fun k => ?_
  obtain ⟨y, hy⟩ := h k
  exact ⟨y i, by rw [hy]; simp⟩

theorem endo_haus [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {T : Module.End 𝓞 (Fin r → 𝓞)}
    (h : ∀ k : ℕ, ∃ S : Module.End 𝓞 (Fin r → 𝓞), T = (p : 𝓞) ^ k • S) : T = 0 := by
  refine LinearMap.ext fun m => ?_
  refine vec_haus p fun k => ?_
  obtain ⟨S, hS⟩ := h k
  exact ⟨S m, by rw [hS]; simp⟩

theorem O_lim [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (a : ℕ → 𝓞) (h : ∀ k : ℕ, (p : 𝓞) ^ k ∣ a (k + 1) - a k) :
    ∃ L : 𝓞, ∀ k : ℕ, (p : 𝓞) ^ k ∣ L - a k := by
  have hmn : ∀ m n : ℕ, m ≤ n → (p : 𝓞) ^ m ∣ a n - a m := by
    intro m n hle
    induction hle with
    | refl => simp
    | @step n hle ih =>
      have h1 : (p : 𝓞) ^ m ∣ a (n + 1) - a n :=
        (pow_dvd_pow (p : 𝓞) (show m ≤ n from hle)).trans (h n)
      have : a (n + 1) - a m = (a (n + 1) - a n) + (a n - a m) := by ring
      rw [this]; exact dvd_add h1 ih
  have hP : IsPrecomplete (Ideal.span {(p : 𝓞)}) 𝓞 := inferInstance
  obtain ⟨L, hL⟩ := hP.prec (f := a)
    (fun {m n} hle => by
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, dvd_sub_comm]
      exact hmn m n hle)
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, dvd_sub_comm] at this
  exact this

theorem mat_lim [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (A : ℕ → Matrix (Fin r) (Fin r) 𝓞)
    (h : ∀ k : ℕ, ∃ B : Matrix (Fin r) (Fin r) 𝓞, A (k + 1) - A k = (p : 𝓞) ^ k • B) :
    ∃ Al : Matrix (Fin r) (Fin r) 𝓞, ∀ k : ℕ, ∃ B : Matrix (Fin r) (Fin r) 𝓞,
      Al - A k = (p : 𝓞) ^ k • B := by
  have hij : ∀ i j : Fin r, ∃ L : 𝓞, ∀ k : ℕ, (p : 𝓞) ^ k ∣ L - A k i j := fun i j =>
    O_lim p (fun k => A k i j) fun k => by
      obtain ⟨B, hB⟩ := h k
      refine ⟨B i j, ?_⟩
      have := congrFun (congrFun hB i) j
      simpa [Matrix.sub_apply, Matrix.smul_apply] using this
  choose L hL using hij
  refine ⟨Matrix.of L, fun k => ?_⟩
  have hc : ∀ i j : Fin r, ∃ c : 𝓞, L i j - A k i j = (p : 𝓞) ^ k * c := fun i j => hL i j k
  choose C hC using hc
  exact ⟨Matrix.of C, by ext i j; simp [hC]⟩

theorem endo_lim [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (T : ℕ → Module.End 𝓞 (Fin r → 𝓞))
    (h : ∀ k : ℕ, ∃ S : Module.End 𝓞 (Fin r → 𝓞), T (k + 1) - T k = (p : 𝓞) ^ k • S) :
    ∃ Tl : Module.End 𝓞 (Fin r → 𝓞), ∀ k : ℕ, ∃ S : Module.End 𝓞 (Fin r → 𝓞),
      Tl - T k = (p : 𝓞) ^ k • S := by
  obtain ⟨Al, hAl⟩ := mat_lim p (fun k => LinearMap.toMatrix' (T k)) fun k => by
    obtain ⟨S, hS⟩ := h k
    exact ⟨LinearMap.toMatrix' S, by rw [← map_sub, hS, map_smul]⟩
  refine ⟨Matrix.toLin' Al, fun k => ?_⟩
  obtain ⟨B, hB⟩ := hAl k
  refine ⟨Matrix.toLin' B, ?_⟩
  calc Matrix.toLin' Al - T k = Matrix.toLin' (Al - LinearMap.toMatrix' (T k)) := by
        rw [map_sub, Matrix.toLin'_toMatrix']
    _ = (p : 𝓞) ^ k • Matrix.toLin' B := by rw [hB, map_smul]

theorem commute_lim [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] {T : ℕ → Module.End 𝓞 (Fin r → 𝓞)} {Tl A : Module.End 𝓞 (Fin r → 𝓞)}
    (hT : ∀ k : ℕ, ∃ S : Module.End 𝓞 (Fin r → 𝓞), Tl - T k = (p : 𝓞) ^ k • S)
    (hc : ∀ k, Commute A (T k)) : Commute A Tl := by
  have h0 : A * Tl - Tl * A = 0 := endo_haus p fun k => by
    obtain ⟨S, hS⟩ := hT k
    refine ⟨A * S - S * A, ?_⟩
    calc A * Tl - Tl * A = A * (Tl - T k) - (Tl - T k) * A := by
          rw [mul_sub, sub_mul, (hc k).eq]; abel
      _ = (p : 𝓞) ^ k • (A * S - S * A) := by rw [hS, mul_smul_comm, smul_mul_assoc, smul_sub]
  show A * Tl = Tl * A
  exact sub_eq_zero.mp h0

end complete

section pigeonhole
variable [Fact p.Prime] [Algebra 𝓞 (ZMod p)]

theorem pow_periodic {A : Type*} [Monoid A] (a : A) {i d : ℕ} (h : a ^ (i + d) = a ^ i) :
    ∀ n t : ℕ, i ≤ n → a ^ (n + t * d) = a ^ n := by
  intro n t hn
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hn
    calc a ^ (i + c + (t + 1) * d) = a ^ (i + d) * a ^ (c + t * d) := by
          rw [← pow_add]; congr 1; ring
      _ = a ^ (i + c + t * d) := by rw [h, ← pow_add]; congr 1; ring
      _ = a ^ (i + c) := ih

noncomputable def redMat (r : ℕ) : Module.End 𝓞 (Fin r → 𝓞) →+* Matrix (Fin r) (Fin r) (ZMod p) :=
  (algebraMap 𝓞 (ZMod p)).mapMatrix.comp
    (LinearMap.toMatrixAlgEquiv' : Module.End 𝓞 (Fin r → 𝓞) ≃ₐ[𝓞] Matrix (Fin r) (Fin r) 𝓞)

theorem redMat_eq_zero (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {T : Module.End 𝓞 (Fin r → 𝓞)} (h : redMat p r T = 0) :
    ∃ S : Module.End 𝓞 (Fin r → 𝓞), T = (p : 𝓞) • S := by
  have hent : ∀ i j : Fin r, ∃ c : 𝓞, LinearMap.toMatrix' T i j = (p : 𝓞) * c := by
    intro i j
    have hij := congrFun (congrFun h i) j
    simp only [redMat, RingHom.coe_comp, Function.comp_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, Matrix.zero_apply] at hij
    have : LinearMap.toMatrix' T i j ∈ RingHom.ker (algebraMap 𝓞 (ZMod p)) := hij
    rw [hker, Ideal.mem_span_singleton] at this
    exact this
  choose C hC using hent
  refine ⟨Matrix.toLin' (Matrix.of C), ?_⟩
  calc T = Matrix.toLin' (LinearMap.toMatrix' T) := (Matrix.toLin'_toMatrix' T).symm
    _ = Matrix.toLin' ((p : 𝓞) • Matrix.of C) := by
        congr 1; ext i j; simp [hC]
    _ = (p : 𝓞) • Matrix.toLin' (Matrix.of C) := by rw [map_smul]

theorem exists_pow_idem_mod (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (F : Module.End 𝓞 (Fin r → 𝓞)) :
    ∃ (N : ℕ) (S : Module.End 𝓞 (Fin r → 𝓞)),
      F ^ (N + 1) * F ^ (N + 1) - F ^ (N + 1) = (p : 𝓞) • S := by
  obtain ⟨i, j, hne, hij⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => redMat p r F ^ n)

  wlog hlt : i < j generalizing i j
  · exact this j i hne.symm hij.symm (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt

  have hper : (redMat p r F) ^ (i + (d + 1)) = (redMat p r F) ^ i := by
    simpa [add_assoc] using hij.symm
  refine ⟨i * (d + 1) + d, ?_⟩
  set N := i * (d + 1) + d + 1 with hN
  have hNi : i ≤ N := by nlinarith
  have h2 : (redMat p r F) ^ (N + N) = (redMat p r F) ^ N := by
    have := pow_periodic (redMat p r F) hper N (i + 1) hNi
    convert this using 2; rw [hN]; ring
  apply redMat_eq_zero p hker
  rw [map_sub, map_mul, map_pow, ← pow_add, h2, sub_self]

end pigeonhole

theorem newton_id1 {A : Type*} [Ring A] (x : A) :
    (3 * x * x - 2 * x * x * x) * (3 * x * x - 2 * x * x * x) - (3 * x * x - 2 * x * x * x) =
      (x * x - x) * (x * x - x) * (4 * x * x - 4 * x - 3) := by
  noncomm_ring

theorem newton_id2 {A : Type*} [Ring A] (x : A) :
    (3 * x * x - 2 * x * x * x) - x = -((2 * x - 1) * (x * x - x)) := by
  noncomm_ring

theorem newton_id3 {A : Type*} [Ring A] (x : A) :
    x * (3 * x - 2 * x * x) = 3 * x * x - 2 * x * x * x := by
  noncomm_ring

theorem newton_id4 {A : Type*} [Ring A] (q x : A) :
    q * (3 * x - 2 * x * x) - q = -((q * (2 * x - 1)) * (x - 1)) := by
  noncomm_ring

def newton {A : Type*} [Ring A] (e₀ : A) : ℕ → A
  | 0 => e₀
  | k + 1 => 3 * newton e₀ k * newton e₀ k - 2 * newton e₀ k * newton e₀ k * newton e₀ k

theorem commute_newton {A : Type*} [Ring A] {e₀ a : A} (h : Commute a e₀) (k : ℕ) :
    Commute a (newton e₀ k) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    show Commute a (3 * newton e₀ k * newton e₀ k - 2 * newton e₀ k * newton e₀ k * newton e₀ k)
    exact (((Commute.ofNat_right a 3).mul_right ih).mul_right ih).sub_right
      ((((Commute.ofNat_right a 2).mul_right ih).mul_right ih).mul_right ih)

theorem newton_sq_sub (e₀ S₀ : Module.End 𝓞 (Fin r → 𝓞)) (h0 : e₀ * e₀ - e₀ = (p : 𝓞) • S₀)
    (k : ℕ) : ∃ S : Module.End 𝓞 (Fin r → 𝓞),
      newton e₀ k * newton e₀ k - newton e₀ k = (p : 𝓞) ^ (k + 1) • S := by
  induction k with
  | zero => exact ⟨S₀, by simp at h0 ⊢; exact h0⟩
  | succ k ih =>
    obtain ⟨S, hS⟩ := ih
    set x := newton e₀ k with hx
    refine ⟨(p : 𝓞) ^ k • (S * S * (4 * x * x - 4 * x - 3)), ?_⟩
    show (3 * x * x - 2 * x * x * x) * (3 * x * x - 2 * x * x * x) - (3 * x * x - 2 * x * x * x) = _
    rw [newton_id1, hS, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
      smul_smul]
    congr 1
    ring

theorem newton_step (e₀ S₀ : Module.End 𝓞 (Fin r → 𝓞)) (h0 : e₀ * e₀ - e₀ = (p : 𝓞) • S₀)
    (k : ℕ) : ∃ S : Module.End 𝓞 (Fin r → 𝓞),
      newton e₀ (k + 1) - newton e₀ k = (p : 𝓞) ^ (k + 1) • S := by
  obtain ⟨S, hS⟩ := newton_sq_sub p e₀ S₀ h0 k
  refine ⟨-((2 * newton e₀ k - 1) * S), ?_⟩
  show (3 * newton e₀ k * newton e₀ k - 2 * newton e₀ k * newton e₀ k * newton e₀ k) - newton e₀ k = _
  rw [newton_id2, hS, mul_smul_comm, smul_neg]

def qseq {A : Type*} [Ring A] (e₀ Q₀ : A) : ℕ → A
  | 0 => Q₀
  | k + 1 => qseq e₀ Q₀ k * (3 * newton e₀ k - 2 * newton e₀ k * newton e₀ k)

theorem newton_eq_mul_qseq {A : Type*} [Ring A] {F e₀ Q₀ : A} (h : e₀ = F * Q₀) (k : ℕ) :
    newton e₀ k = F * qseq e₀ Q₀ k := by
  induction k with
  | zero => exact h
  | succ k ih =>
    show 3 * newton e₀ k * newton e₀ k - 2 * newton e₀ k * newton e₀ k * newton e₀ k =
      F * (qseq e₀ Q₀ k * (3 * newton e₀ k - 2 * newton e₀ k * newton e₀ k))
    rw [← mul_assoc, ← ih, newton_id3]

theorem commute_qseq {A : Type*} [Ring A] {e₀ Q₀ a : A} (hQ : Commute a Q₀) (he : Commute a e₀)
    (k : ℕ) : Commute a (qseq e₀ Q₀ k) := by
  induction k with
  | zero => exact hQ
  | succ k ih =>
    have hx := commute_newton he k
    exact ih.mul_right (((Commute.ofNat_right a 3).mul_right hx).sub_right
      (((Commute.ofNat_right a 2).mul_right hx).mul_right hx))

theorem qseq_step (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {F V e₀ Q₀ S₀ : Module.End 𝓞 (Fin r → 𝓞)}
    (hVF : V * F = (p : 𝓞) • (1 : Module.End 𝓞 (Fin r → 𝓞))) (he : e₀ = F * Q₀)
    (hFQ : Commute F Q₀) (h0 : e₀ * e₀ - e₀ = (p : 𝓞) • S₀) (k : ℕ) :
    ∃ S : Module.End 𝓞 (Fin r → 𝓞), qseq e₀ Q₀ (k + 1) - qseq e₀ Q₀ k = (p : 𝓞) ^ k • S := by
  obtain ⟨S, hS⟩ := newton_sq_sub p e₀ S₀ h0 k
  set x := newton e₀ k with hx
  set q := qseq e₀ Q₀ k with hq
  have hxq : x = F * q := newton_eq_mul_qseq he k
  have hFe : Commute F e₀ := by rw [he]; exact (Commute.refl F).mul_right hFQ
  have hFq : Commute F q := commute_qseq hFQ hFe k
  have hqx : Commute q x := by rw [hxq]; exact hFq.symm.mul_right (Commute.refl q)
  have hkey : q * x - q = (p : 𝓞) ^ k • (V * S) := by
    apply endo_cancel p hp
    calc (p : 𝓞) • (q * x - q) = V * F * (q * x - q) := by rw [hVF, smul_mul_assoc, one_mul]
      _ = V * (x * x - x) := by rw [hxq, mul_assoc V F, mul_sub, ← mul_assoc F q]
      _ = (p : 𝓞) • ((p : 𝓞) ^ k • (V * S)) := by rw [hS, mul_smul_comm, smul_smul, ← pow_succ']
  refine ⟨-((2 * x - 1) * (V * S)), ?_⟩
  show q * (3 * x - 2 * x * x) - q = _
  rw [newton_id4]
  have h2 : q * (2 * x - 1) = (2 * x - 1) * q :=
    (((Commute.ofNat_right q 2).mul_right hqx).sub_right (Commute.one_right q)).eq
  rw [h2, mul_assoc, show q * (x - 1) = q * x - q by rw [mul_sub, mul_one], hkey, mul_smul_comm,
    smul_neg]

theorem exists_idempotent (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Fact p.Prime] [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (F V : Module.End 𝓞 (Fin r → 𝓞)) (hVF : V * F = (p : 𝓞) • (1 : Module.End 𝓞 (Fin r → 𝓞)))
    (hFV : F * V = (p : 𝓞) • (1 : Module.End 𝓞 (Fin r → 𝓞))) :
    ∃ (N : ℕ) (e Q R : Module.End 𝓞 (Fin r → 𝓞)),
      e * e = e ∧ Commute F e ∧ Commute V e ∧ e = F * Q ∧ Commute F Q ∧
      F ^ (N + 1) = e + (p : 𝓞) • R ∧ Commute e R := by
  obtain ⟨N, S₀, h0⟩ := exists_pow_idem_mod p hker F
  set e₀ := F ^ (N + 1) with he₀def

  obtain ⟨e, he⟩ := endo_lim p (newton e₀) fun k => by
    obtain ⟨S, hS⟩ := newton_step p e₀ S₀ h0 k
    exact ⟨(p : 𝓞) • S, by rw [hS, smul_smul, pow_succ]⟩
  have he' : ∀ k : ℕ, ∃ S : Module.End 𝓞 (Fin r → 𝓞),
      e - newton e₀ k = (p : 𝓞) ^ (k + 1) • S := fun k => by
    obtain ⟨S1, h1⟩ := he (k + 1)
    obtain ⟨S2, h2⟩ := newton_step p e₀ S₀ h0 k
    exact ⟨S1 + S2, by rw [smul_add, ← h1, ← h2]; abel⟩
  have hFe₀ : Commute F e₀ := (Commute.refl F).pow_right _
  have hVF' : Commute V F := by show V * F = F * V; rw [hVF, hFV]
  have hVe₀ : Commute V e₀ := hVF'.pow_right _
  have hFe : Commute F e := commute_lim p he (commute_newton hFe₀)
  have hVe : Commute V e := commute_lim p he (commute_newton hVe₀)
  have hee : e * e = e := by
    apply sub_eq_zero.mp
    apply endo_haus p
    intro k
    obtain ⟨S, hS⟩ := he k
    obtain ⟨S', hS'⟩ := newton_sq_sub p e₀ S₀ h0 k
    refine ⟨e * S + S * newton e₀ k - S + (p : 𝓞) • S', ?_⟩
    calc e * e - e = e * (e - newton e₀ k) + (e - newton e₀ k) * newton e₀ k - (e - newton e₀ k) +
          (newton e₀ k * newton e₀ k - newton e₀ k) := by simp only [mul_sub, sub_mul]; abel
      _ = (p : 𝓞) ^ k • (e * S + S * newton e₀ k - S + (p : 𝓞) • S') := by
          rw [hS, hS']
          simp only [smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, pow_succ]

  have hQ₀ : e₀ = F * F ^ N := by rw [he₀def, pow_succ']
  have hFFN : Commute F (F ^ N) := (Commute.refl F).pow_right N
  obtain ⟨Q, hQ⟩ := endo_lim p (qseq e₀ (F ^ N)) (qseq_step p hp hVF hQ₀ hFFN h0)
  have hFQ : Commute F Q := commute_lim p hQ (commute_qseq hFFN hFe₀)
  have heFQ : e = F * Q := by
    apply sub_eq_zero.mp
    apply endo_haus p
    intro k
    obtain ⟨S, hS⟩ := he k
    obtain ⟨S', hS'⟩ := hQ k
    refine ⟨S - F * S', ?_⟩
    calc e - F * Q = (e - newton e₀ k) - F * (Q - qseq e₀ (F ^ N) k) := by
          rw [newton_eq_mul_qseq hQ₀ k, mul_sub]; abel
      _ = (p : 𝓞) ^ k • (S - F * S') := by rw [hS, hS', mul_smul_comm, smul_sub]

  obtain ⟨S1, hS1⟩ := he' 0
  have hS1' : e - e₀ = (p : 𝓞) • S1 := by simp at hS1; exact hS1
  set R := -S1 with hRdef
  have hR : (p : 𝓞) • R = e₀ - e := by rw [hRdef, smul_neg, ← hS1', neg_sub]
  refine ⟨N, e, Q, R, hee, hFe, hVe, heFQ, hFQ, ?_, ?_⟩
  · rw [hR]; abel
  · show e * R = R * e
    apply endo_cancel p hp
    have hc : e₀ * e = e * e₀ := (hFe.pow_left (N + 1)).eq
    calc (p : 𝓞) • (e * R) = e * ((p : 𝓞) • R) := (mul_smul_comm _ _ _).symm
      _ = e * (e₀ - e) := by rw [hR]
      _ = (e₀ - e) * e := by rw [mul_sub, sub_mul, hc]
      _ = (p : 𝓞) • R * e := by rw [hR]
      _ = (p : 𝓞) • (R * e) := smul_mul_assoc _ _ _

end Deformation.HondaSystem.SplitM

open Deformation.HondaSystem.SplitM in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (r : ℕ) (H₁ : Deformation.HondaSystem (p : 𝓞) (Fin r → 𝓞)) :
    ∃ (Mc Met : Submodule 𝓞 (Fin r → 𝓞)) (hc : IsCompl Mc Met),

      (∀ m ∈ Mc, H₁.F m ∈ Mc ∧ H₁.V m ∈ Mc) ∧ (∀ m ∈ Met, H₁.F m ∈ Met ∧ H₁.V m ∈ Met) ∧

      (∃ N : ℕ, ∀ m ∈ Mc, ∃ y ∈ Mc, (H₁.F ^ N) m = (p : 𝓞) • y) ∧
      (∀ m ∈ Met, ∃ m' ∈ Met, H₁.F m' = m) ∧ Met ≤ LinearMap.range H₁.F ∧

      (∀ m, m ∈ Met ↔ ∀ N : ℕ, ∃ y, (H₁.F ^ N) y = m) ∧
      (∀ m, m ∈ Mc ↔ ∀ k : ℕ, ∃ N : ℕ, ∃ y, (H₁.F ^ N) m = (p : 𝓞) ^ k • y) ∧

      Module.Free 𝓞 Mc ∧ Module.Free 𝓞 Met ∧ Module.finrank 𝓞 Mc + Module.finrank 𝓞 Met = r ∧

      H₁.L ⊓ Met = ⊥ ∧

      (∀ x ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        x ∈ LinearMap.range H₁.F →
          ∃ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc), x = (p : 𝓞) • y) ∧
      (∀ y ∈ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc),
        (p : 𝓞) • y ∈ LinearMap.range H₁.F) ∧
      LinearMap.range H₁.F ⊔ (H₁.L).map (Mc.subtype ∘ₗ Submodule.projectionOnto Mc Met hc) = ⊤ := by
  classical
  have hVF : H₁.V * H₁.F = (p : 𝓞) • (1 : Module.End 𝓞 (Fin r → 𝓞)) := H₁.vf
  have hFV : H₁.F * H₁.V = (p : 𝓞) • (1 : Module.End 𝓞 (Fin r → 𝓞)) := H₁.fv
  obtain ⟨N, e, Q, R, hee, hFe, hVe, heFQ, hFQ, he₀, heR⟩ :=
    exists_idempotent p hp hker H₁.F H₁.V hVF hFV

  set T : Module.End 𝓞 (Fin r → 𝓞) := 1 - e with hTdef
  have hT : IsIdempotentElem T := by
    show (1 - e) * (1 - e) = 1 - e
    rw [mul_sub, mul_one, sub_mul, one_mul, hee, sub_self, sub_zero]
  have hTapp : ∀ m, T m = m - e m := fun m => rfl
  have hc : IsCompl (LinearMap.range T) (LinearMap.ker T) := LinearMap.IsIdempotentElem.isCompl hT

  have heapp : ∀ m, e (e m) = e m := fun m => by rw [← Module.End.mul_apply, hee]
  have hFe_app : ∀ m, e (H₁.F m) = H₁.F (e m) := fun m => by
    show (e * H₁.F) m = (H₁.F * e) m; rw [hFe.eq]
  have hFne_app : ∀ (n : ℕ) m, e ((H₁.F ^ n) m) = (H₁.F ^ n) (e m) := fun n m => by
    show (e * H₁.F ^ n) m = (H₁.F ^ n * e) m; rw [(hFe.pow_left n).eq]
  have hVe_app : ∀ m, e (H₁.V m) = H₁.V (e m) := fun m => by
    show (e * H₁.V) m = (H₁.V * e) m; rw [hVe.eq]
  have heQ : ∀ m, e m = H₁.F (Q m) := fun m => by rw [heFQ]; rfl
  have hQe : Q * e = e * Q := by rw [heFQ, ← mul_assoc, ← hFQ.eq, mul_assoc]
  have hQF : ∀ m, e m = m → Q (H₁.F m) = m := fun m hm => by
    rw [← Module.End.mul_apply, ← hFQ.eq, ← heFQ]; exact hm
  have hQFn : ∀ (n : ℕ) m, e m = m → (Q ^ n) ((H₁.F ^ n) m) = m := by
    intro n
    induction n with
    | zero => intro m _; simp
    | succ n ih =>
      intro m hm
      have hFn : e ((H₁.F ^ n) m) = (H₁.F ^ n) m := by rw [hFne_app, hm]
      rw [pow_succ, pow_succ', Module.End.mul_apply, Module.End.mul_apply, hQF _ hFn, ih m hm]

  have hMet : ∀ m, m ∈ LinearMap.ker T ↔ e m = m := fun m => by
    rw [LinearMap.mem_ker, hTapp, sub_eq_zero, eq_comm]
  have hMc : ∀ m, m ∈ LinearMap.range T ↔ e m = 0 := fun m => by
    rw [LinearMap.IsIdempotentElem.mem_range_iff hT, hTapp, sub_eq_self]
  have hproj : (LinearMap.range T).subtype ∘ₗ Submodule.projectionOnto _ _ hc = T :=
    (LinearMap.IsIdempotentElem.eq_projection hT).symm

  have hTe : T * e = 0 := by show (1 - e) * e = 0; rw [sub_mul, one_mul, hee, sub_self]
  have hTe₀ : T * H₁.F ^ (N + 1) = (p : 𝓞) • (T * R) := by
    rw [he₀, mul_add, mul_smul_comm, hTe, zero_add]
  have hTc : Commute (H₁.F ^ (N + 1)) T := (Commute.one_right _).sub_right (hFe.pow_left _)
  have hTR : Commute T R := (Commute.one_left R).sub_left heR
  have hTRT : T * R * T = T * R := by rw [mul_assoc, ← hTR.eq, ← mul_assoc, (show T * T = T from hT)]
  have hTpow : ∀ k : ℕ, T * (H₁.F ^ (N + 1)) ^ k = (p : 𝓞) ^ k • ((T * R) ^ k * T) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc T * (H₁.F ^ (N + 1)) ^ (k + 1) = T * (H₁.F ^ (N + 1)) ^ k * H₁.F ^ (N + 1) := by
            rw [pow_succ, mul_assoc]
        _ = (p : 𝓞) ^ k • ((T * R) ^ k * (T * H₁.F ^ (N + 1))) := by
            rw [ih, smul_mul_assoc, mul_assoc]
        _ = (p : 𝓞) ^ k • ((T * R) ^ k * ((p : 𝓞) • (T * R))) := by rw [hTe₀]
        _ = (p : 𝓞) ^ (k + 1) • ((T * R) ^ (k + 1) * T) := by
            rw [mul_smul_comm, smul_smul, ← pow_succ, pow_succ (T * R), mul_assoc ((T * R) ^ k),
              hTRT]

  haveI : (Ideal.span {(p : 𝓞)}).IsMaximal := by
    rw [← hker]; exact RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective _)
  haveI : IsLocalRing 𝓞 := isLocalRing_of_isAdicComplete_maximal (Ideal.span {(p : 𝓞)})
  have hfinMc : Module.Finite 𝓞 (LinearMap.range T) :=
    Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc)
  have hfinMet : Module.Finite 𝓞 (LinearMap.ker T) :=
    Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  have hprMc : Module.Projective 𝓞 (LinearMap.range T) :=
    Module.Projective.of_split _ _ (Submodule.projectionOnto_comp_subtype hc)
  have hprMet : Module.Projective 𝓞 (LinearMap.ker T) :=
    Module.Projective.of_split _ _ (Submodule.projectionOnto_comp_subtype hc.symm)
  have hfrMc : Module.Free 𝓞 (LinearMap.range T) := Module.free_of_flat_of_isLocalRing
  have hfrMet : Module.Free 𝓞 (LinearMap.ker T) := Module.free_of_flat_of_isLocalRing
  have hrank : Module.finrank 𝓞 (LinearMap.range T) + Module.finrank 𝓞 (LinearMap.ker T) = r := by
    have h := LinearEquiv.finrank_eq (Submodule.prodEquivOfIsCompl _ _ hc)
    rw [Module.finrank_prod, Module.finrank_fin_fun] at h
    exact h
  refine ⟨LinearMap.range T, LinearMap.ker T, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfrMc, hfrMet, hrank,
    ?_, ?_, ?_, ?_⟩
  ·
    intro m hm
    rw [hMc] at hm
    refine ⟨(hMc _).2 ?_, (hMc _).2 ?_⟩
    · rw [hFe_app, hm, map_zero]
    · rw [hVe_app, hm, map_zero]
  ·
    intro m hm
    rw [hMet] at hm
    exact ⟨(hMet _).2 (by rw [hFe_app, hm]), (hMet _).2 (by rw [hVe_app, hm])⟩
  ·
    refine ⟨N + 1, fun m hm => ?_⟩
    rw [hMc] at hm
    have hpR : (p : 𝓞) • R = H₁.F ^ (N + 1) - e := by rw [he₀]; abel
    refine ⟨R m, (hMc _).2 ?_, ?_⟩
    · apply vec_cancel p hp
      rw [smul_zero]
      calc (p : 𝓞) • e (R m) = e (((p : 𝓞) • R) m) := by rw [LinearMap.smul_apply, map_smul]
        _ = e ((H₁.F ^ (N + 1)) m) - e (e m) := by rw [hpR, LinearMap.sub_apply, map_sub]
        _ = 0 := by rw [hFne_app, hm, map_zero, map_zero, sub_zero]
    · rw [he₀, LinearMap.add_apply, LinearMap.smul_apply, hm, zero_add]
  ·
    intro m hm
    rw [hMet] at hm
    refine ⟨Q m, (hMet _).2 ?_, by rw [← heQ, hm]⟩
    show (e * Q) m = Q m
    rw [← hQe, Module.End.mul_apply, hm]
  ·
    intro m hm
    rw [hMet] at hm
    exact LinearMap.mem_range.2 ⟨Q m, by rw [← heQ, hm]⟩
  ·
    intro m
    rw [hMet]
    constructor
    · intro hm n
      induction n generalizing m with
      | zero => exact ⟨m, by simp⟩
      | succ n ih =>
        have hQm : e (Q m) = Q m := by
          show (e * Q) m = Q m; rw [← hQe, Module.End.mul_apply, hm]
        obtain ⟨y, hy⟩ := ih (Q m) hQm
        exact ⟨y, by rw [pow_succ', Module.End.mul_apply, hy, ← heQ, hm]⟩
    · intro h
      have hTm : T m = 0 := vec_haus p fun k => by
        obtain ⟨y, hy⟩ := h ((N + 1) * k)
        exact ⟨((T * R) ^ k * T) y, by
          rw [← hy, pow_mul, ← Module.End.mul_apply, hTpow, LinearMap.smul_apply]⟩
      rw [hTapp, sub_eq_zero] at hTm
      exact hTm.symm
  ·
    intro m
    rw [hMc]
    constructor
    · intro hm k
      have hTm : T m = m := by rw [hTapp, hm, sub_zero]
      refine ⟨(N + 1) * k, ((T * R) ^ k * T) m, ?_⟩
      calc (H₁.F ^ ((N + 1) * k)) m = ((H₁.F ^ (N + 1)) ^ k) (T m) := by rw [pow_mul, hTm]
        _ = (T * (H₁.F ^ (N + 1)) ^ k) m := by
            rw [← Module.End.mul_apply, (hTc.pow_left k).eq]
        _ = (p : 𝓞) ^ k • ((T * R) ^ k * T) m := by rw [hTpow, LinearMap.smul_apply]
    · intro h
      refine vec_haus p fun k => ?_
      obtain ⟨n, y, hy⟩ := h k
      refine ⟨(Q ^ n) (e y), ?_⟩
      calc e m = (Q ^ n) ((H₁.F ^ n) (e m)) := (hQFn n (e m) (heapp m)).symm
        _ = (Q ^ n) (e ((H₁.F ^ n) m)) := by rw [hFne_app]
        _ = (p : 𝓞) ^ k • (Q ^ n) (e y) := by rw [hy, map_smul, map_smul]
  ·
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxM⟩ := Submodule.mem_inf.mp hx
    rw [hMet] at hxM
    have key : ∀ k : ℕ, ∀ x, x ∈ H₁.L → e x = x → ∃ y, x = (p : 𝓞) ^ k • y := by
      intro k
      induction k with
      | zero => intro x _ _; exact ⟨x, by simp⟩
      | succ k ih =>
        intro x hxL hex
        obtain ⟨y₁, hy₁L, hxy⟩ :=
          H₁.sh1_le x hxL (LinearMap.mem_range.2 ⟨Q x, by rw [← heQ, hex]⟩)
        have hey : e y₁ = y₁ := vec_cancel p hp (by rw [← map_smul, ← hxy, hex])
        obtain ⟨z, hz⟩ := ih y₁ hy₁L hey
        exact ⟨z, by rw [hxy, hz, smul_smul, pow_succ']⟩
    exact vec_haus p fun k => key k x hxL hxM
  ·
    rw [hproj]
    intro x hx hxF
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp hx
    have hlF : l ∈ LinearMap.range H₁.F := by
      have : l = T l + e l := by rw [hTapp]; abel
      rw [this]
      exact add_mem hxF (LinearMap.mem_range.2 ⟨Q l, (heQ l).symm⟩)
    obtain ⟨l', hl', hll'⟩ := H₁.sh1_le l hl hlF
    exact ⟨T l', Submodule.mem_map_of_mem hl', by rw [hll', map_smul]⟩
  ·
    rw [hproj]
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.mp hy
    rw [hTapp, smul_sub]
    refine sub_mem (H₁.sh1_ge l hl) ?_
    rw [← map_smul, heQ]
    exact LinearMap.mem_range_self _ _
  ·
    rw [hproj, eq_top_iff]
    intro m _
    have hm : m ∈ LinearMap.range H₁.F ⊔ H₁.L := by rw [H₁.sh2']; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hm
    refine Submodule.mem_sup.mpr ⟨a + e b, add_mem ha (LinearMap.mem_range.2 ⟨Q b, (heQ b).symm⟩),
      T b, Submodule.mem_map_of_mem hb, ?_⟩
    rw [hTapp, ← hab]
    abel

end S_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot
end P2MW
export P2MW.S_Deformation_HondaSystem_exists_isCompl_pow_F_le_and_L_inf_eq_bot (solution)
