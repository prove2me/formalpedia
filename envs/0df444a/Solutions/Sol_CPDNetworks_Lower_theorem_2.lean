-- Prove2me | solution 1 for CPDNetworks.Lower.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T23:06:32.789253+00:00
-- url     : https://prove2.me/submissions/c9b91a32-20fb-4c06-98ab-f3f1abf6e94e

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

set_option autoImplicit false

namespace CPDNW2

open CPDNetworks.Lower HighDimProb.RandomMatrices
open scoped Matrix

noncomputable def S {n : ℕ} (b : Fin n → Bool) : ℝ := ∑ i, sgn b i

lemma sgn_sq {n : ℕ} (b : Fin n → Bool) (i : Fin n) : sgn b i * sgn b i = 1 := by
  unfold sgn; split_ifs <;> norm_num

noncomputable def G (n : ℕ) (l : ℝ) : ℝ :=
  ∑ b : Fin n → Bool, Real.exp (l * (S b ^ 2 - n) / 2)

lemma S_cons {n : ℕ} (b0 : Bool) (b : Fin n → Bool) :
    S (Fin.cons b0 b : Fin (n+1) → Bool) = (if b0 then 1 else -1) + S b := by
  simp [S, Fin.sum_univ_succ, sgn]

lemma sum_cons {n : ℕ} (f : (Fin (n+1) → Bool) → ℝ) :
    ∑ b, f b = ∑ b0 : Bool, ∑ b : Fin n → Bool, f (Fin.cons b0 b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Bool) _ _ (fun _ => rfl)).symm

lemma step_term (l s n : ℝ) :
    Real.exp (l * ((1 + s) ^ 2 - (n + 1)) / 2) + Real.exp (l * ((-1 + s) ^ 2 - (n + 1)) / 2)
      ≤ 2 * Real.exp (l ^ 2 * n / 2) * Real.exp ((l + l ^ 2) * (s ^ 2 - n) / 2) := by
  have e1 : l * ((1 + s) ^ 2 - (n + 1)) / 2 = l * (s ^ 2 - n) / 2 + l * s := by ring
  have e2 : l * ((-1 + s) ^ 2 - (n + 1)) / 2 = l * (s ^ 2 - n) / 2 + -(l * s) := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  have hc : Real.exp (l * s) + Real.exp (-(l * s)) = 2 * Real.cosh (l * s) := by
    rw [Real.cosh_eq]; ring
  have hb := Real.cosh_le_exp_half_sq (l * s)
  have hpos := Real.exp_pos (l * (s ^ 2 - n) / 2)
  calc Real.exp (l * (s ^ 2 - n) / 2) * Real.exp (l * s)
        + Real.exp (l * (s ^ 2 - n) / 2) * Real.exp (-(l * s))
      = 2 * Real.exp (l * (s ^ 2 - n) / 2) * Real.cosh (l * s) := by
        rw [← mul_add, hc]; ring
    _ ≤ 2 * Real.exp (l * (s ^ 2 - n) / 2) * Real.exp ((l * s) ^ 2 / 2) := by gcongr
    _ = 2 * Real.exp (l ^ 2 * n / 2) * Real.exp ((l + l ^ 2) * (s ^ 2 - n) / 2) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]; congr 2; ring

lemma G_step (n : ℕ) (l : ℝ) :
    G (n+1) l ≤ 2 * Real.exp (l ^ 2 * n / 2) * G n (l + l ^ 2) := by
  unfold G
  rw [sum_cons, Fintype.sum_bool, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  simp only [S_cons, if_true, Bool.false_eq_true, if_false]
  push_cast
  exact step_term l (S b) n

lemma alg_ineq (l n : ℝ) (hl : 0 ≤ l) (hn : 0 ≤ n) (h : 2 * l * n < 1) :
    l ^ 2 * n / 2 + (l + l ^ 2) ^ 2 * n * (n - 1) / (2 * (1 - 2 * (l + l ^ 2) * (n - 1)))
      ≤ l ^ 2 * (n + 1) * n / (2 * (1 - 2 * l * n)) := by
  have hD2 : 0 < 1 - 2 * l * n := by linarith
  have hll : 2 * l ^ 2 * n ≤ l := by nlinarith
  have hD1 : 0 < 1 - 2 * (l + l ^ 2) * (n - 1) := by nlinarith
  rw [div_add_div _ _ (by norm_num) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have key : 0 ≤ n * (1 + 2 * l) * (1 - 2 * (l + l ^ 2) * (n - 1))
      - (1 + l) ^ 2 * (n - 1) * (1 - 2 * l * n) := by
    have hk : (n - 1) * l ≤ 1 / 2 := by nlinarith
    nlinarith [mul_nonneg hl hn, mul_nonneg (mul_nonneg hl hl) hn, mul_nonneg (mul_nonneg hl hn) hn,
      mul_nonneg (mul_nonneg (mul_nonneg hl hl) hn) hn, mul_nonneg (mul_nonneg (mul_nonneg hl hl) hl) hn,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hl hl) hl) hn) hn]
  have : 0 ≤ l ^ 2 * n * (n * (1 + 2 * l) * (1 - 2 * (l + l ^ 2) * (n - 1))
      - (1 + l) ^ 2 * (n - 1) * (1 - 2 * l * n)) := by positivity
  nlinarith [this]

lemma G_le (n : ℕ) : ∀ l : ℝ, 0 ≤ l → 2 * l * ((n:ℝ) - 1) < 1 →
    G n l ≤ 2 ^ n * Real.exp (l ^ 2 * n * ((n:ℝ) - 1) / (2 * (1 - 2 * l * ((n:ℝ) - 1)))) := by
  induction n with
  | zero => intro l _ _; simp [G, S]
  | succ n ih =>
    intro l hl hcond
    push_cast at hcond ⊢
    have hc' : 2 * l * (n : ℝ) < 1 := by linarith
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hll : 2 * l ^ 2 * n ≤ l := by nlinarith
    have hih := ih (l + l ^ 2) (by positivity) (by nlinarith)
    refine (G_step n l).trans ?_
    have e : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [e]
    calc 2 * Real.exp (l ^ 2 * n / 2) * G n (l + l ^ 2)
        ≤ 2 * Real.exp (l ^ 2 * n / 2) * (2 ^ n * Real.exp ((l + l ^ 2) ^ 2 * n * ((n:ℝ) - 1) /
            (2 * (1 - 2 * (l + l ^ 2) * ((n:ℝ) - 1))))) := by gcongr
      _ = 2 * 2 ^ n * Real.exp (l ^ 2 * n / 2 + (l + l ^ 2) ^ 2 * n * ((n:ℝ) - 1) /
            (2 * (1 - 2 * (l + l ^ 2) * ((n:ℝ) - 1)))) := by rw [Real.exp_add]; ring
      _ ≤ 2 * 2 ^ n * Real.exp (l ^ 2 * (n + 1) * (n + 1 - 1) / (2 * (1 - 2 * l * (n + 1 - 1)))) := by
          gcongr
          have := alg_ineq l n hl hn hc'
          simpa using this

lemma pair_sum_eq {n : ℕ} (g : Fin n → Fin n → ℝ) :
    ∑ p : Pair n, g p.1.1 p.1.2 = ∑ i, ∑ j, if i < j then g i j else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin n × Fin n => x.1 < x.2))
    (by simp) (fun x => g x.1 x.2)]
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

lemma full_sum_eq {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = ∑ i, f i i + 2 * ∑ p : Pair n, f p.1.1 p.1.2 := by
  rw [pair_sum_eq]
  have hpt : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f j i else 0)
      + (if i = j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le, hf i j]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
  simp [Finset.sum_ite_eq]
  ring

lemma chaos_eq {n : ℕ} (b : Fin n → Bool) :
    ∑ p : Pair n, sgn b p.1.1 * sgn b p.1.2 = (S b ^ 2 - n) / 2 := by
  have h := full_sum_eq (fun i j => sgn b i * sgn b j) (fun i j => mul_comm _ _)
  simp only [sgn_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  have hS : S b ^ 2 = ∑ i, ∑ j, sgn b i * sgn b j := by
    rw [sq, S, Finset.sum_mul_sum]
  rw [hS, h]; ring

lemma sgn_xor {n : ℕ} (b c : Fin n → Bool) (i : Fin n) :
    sgn (fun k => xor (b k) (c k)) i = -(sgn b i * sgn c i) := by
  show (if xor (b i) (c i) = true then (1:ℝ) else -1)
    = -((if b i = true then 1 else -1) * (if c i = true then 1 else -1))
  cases b i <;> cases c i <;> norm_num

lemma sum_xor {n : ℕ} (c : Fin n → Bool) (F : (Fin n → Bool) → ℝ) :
    ∑ b : Fin n → Bool, F (fun k => xor (b k) (c k)) = ∑ b, F b := by
  have hinv : Function.Involutive (fun (b : Fin n → Bool) => fun k => xor (b k) (c k)) := by
    intro b; funext k; simp
  exact Fintype.sum_equiv hinv.toPerm _ _ (fun _ => rfl)

/-- the off-diagonal sign matrix -/
noncomputable def sgnMat {n : ℕ} (H : ℝ) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else H * sgn b i * sgn b j

lemma sgnMat_mulVec {n : ℕ} (H : ℝ) (b : Fin n → Bool) :
    sgnMat H b *ᵥ (fun i => sgn b i) = (H * ((n : ℝ) - 1)) • (fun i => sgn b i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, sgnMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  have : ∀ j, (if i = j then (0:ℝ) else H * sgn b i * sgn b j) * sgn b j
      = H * sgn b i - (if i = j then H * sgn b i else 0) := by
    intro j
    split_ifs with h
    · subst h; ring
    · rw [mul_assoc, sgn_sq]; ring
  simp_rw [this]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq]
  ring

lemma opNorm_ge {n : ℕ} (hn : 1 ≤ n) (H : ℝ) (hH : 0 ≤ H) (b : Fin n → Bool) :
    H * ((n : ℝ) - 1) ≤ matrixOpNorm (sgnMat H b) := by
  unfold matrixOpNorm
  set A := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (sgnMat H b)) :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  set x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => sgn b i)
  have hAx : A x = (H * ((n : ℝ) - 1)) • x := by
    show WithLp.toLp 2 (sgnMat H b *ᵥ (fun i => sgn b i)) = _
    rw [sgnMat_mulVec]; rfl
  have hx : x ≠ 0 := by
    intro h0
    have := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨0, hn⟩) h0
    simp [x, sgn] at this
    split_ifs at this <;> norm_num at this
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hle := A.le_opNorm x
  rw [hAx, norm_smul, Real.norm_eq_abs] at hle
  have hc : 0 ≤ H * ((n : ℝ) - 1) := by
    apply mul_nonneg hH; have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [abs_of_nonneg hc] at hle
  exact le_of_mul_le_mul_right hle hxpos


lemma sum_obs_prod {n T : ℕ} (f : Fin T → Pair n → Bool → ℝ) :
    ∑ y : Obs n T, ∏ t, ∏ p, f t p (y t p) = ∏ t, ∏ p, ∑ b, f t p b := by
  simp_rw [Fintype.prod_sum]

lemma bern_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (b : Bool) : 0 ≤ bern x b := by
  unfold bern; split_ifs <;> linarith

lemma weight_nonneg {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ t (p : Pair n), 0 ≤ B t p.1.1 p.1.2 ∧ B t p.1.1 p.1.2 ≤ 1) (y : Obs n T) :
    0 ≤ weight B y := by
  unfold weight
  exact Finset.prod_nonneg fun t _ => Finset.prod_nonneg fun p _ =>
    bern_nonneg (hB t p).1 (hB t p).2 _

lemma sum_weight {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ) :
    ∑ y, weight B y = 1 := by
  unfold weight
  rw [sum_obs_prod (fun t p b => bern (B t p.1.1 p.1.2) b)]
  simp [bern]

lemma prob_le_one {n T : ℕ} (B : Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ t (p : Pair n), 0 ≤ B t p.1.1 p.1.2 ∧ B t p.1.1 p.1.2 ≤ 1) (E : Obs n T → Prop) :
    prob B E ≤ 1 := by
  classical
  unfold prob
  rw [← sum_weight B]
  apply Finset.sum_le_sum
  intro y _
  split_ifs
  · exact le_refl _
  · exact weight_nonneg B hB y

lemma InS_entries {n T : ℕ} {ω : ℝ} {Θ Pm : Matrix (Fin n) (Fin n) ℝ} (h : InS ω Θ Pm)
    (t : Fin T) (p : Pair n) :
    0 ≤ (Pm ⊙ Θ) p.1.1 p.1.2 ∧ (Pm ⊙ Θ) p.1.1 p.1.2 ≤ 1 := by
  obtain ⟨⟨⟨_, hΘ⟩, _⟩, ⟨⟨_, hP⟩, _⟩, _⟩ := h
  have a := hΘ p.1.1 p.1.2
  have b := hP p.1.1 p.1.2
  simp only [Matrix.hadamard_apply]
  constructor
  · exact mul_nonneg b.1 a.1
  · calc Pm p.1.1 p.1.2 * Θ p.1.1 p.1.2 ≤ 1 * 1 := by
          apply mul_le_mul b.2 a.2 a.1 (by norm_num)
      _ = 1 := by norm_num

lemma bdd_typeI {n T : ℕ} (ω : ℝ) (ψ : Obs n T → Bool) :
    BddAbove {p | ∃ Θ Pm, InS ω Θ Pm ∧ p = prob (nullParam (T := T) Θ Pm) (fun y => ψ y = true)} := by
  refine ⟨1, ?_⟩
  rintro x ⟨Θ, Pm, h, rfl⟩
  exact prob_le_one _ (fun t p => InS_entries (T := T) h t p) _

lemma bdd_typeII {n T : ℕ} (D : Finset ℕ) (ω R : ℝ) (ψ : Obs n T → Bool) :
    BddAbove {p | ∃ τ ∈ D, ∃ Θa Θb Pm, InW T τ ω R Θa Θb Pm ∧
      p = prob (altParam (T := T) τ Θa Θb Pm) (fun y => ψ y = false)} := by
  refine ⟨1, ?_⟩
  rintro x ⟨τ, _, Θa, Θb, Pm, h, rfl⟩
  apply prob_le_one
  intro t p
  unfold altParam
  split_ifs
  · exact InS_entries (T := T) h.2.1 t p
  · exact InS_entries (T := T) h.1 t p

/-- total-variation / chi-square bound for a test -/
lemma tv_bound {α : Type*} [Fintype α] (p0 m : α → ℝ) (A : α → Prop) [DecidablePred A]
    (hp0 : ∀ y, 0 < p0 y) (hs0 : ∑ y, p0 y = 1) (hsm : ∑ y, m y = 1) (c : ℝ) (hc : 0 ≤ c)
    (hchi : ∑ y, m y ^ 2 / p0 y ≤ 1 + c ^ 2) :
    1 - c / 2 ≤ ∑ y, (if A y then p0 y else 0) + ∑ y, (if A y then 0 else m y) := by
  have hpt : ∀ y, (p0 y + m y - |p0 y - m y|) / 2 ≤
      (if A y then p0 y else 0) + (if A y then 0 else m y) := by
    intro y
    have := hp0 y
    have h1 := le_abs_self (p0 y - m y)
    have h2 := neg_abs_le (p0 y - m y)
    split_ifs
    · simp; linarith
    · simp; linarith
  have hsum := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpt y)
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hs0, hsm] at hsum
  rw [← Finset.sum_add_distrib]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => Real.sqrt (p0 y))
    (fun y => |p0 y - m y| / Real.sqrt (p0 y))
  have e1 : ∀ y, Real.sqrt (p0 y) * (|p0 y - m y| / Real.sqrt (p0 y)) = |p0 y - m y| := by
    intro y
    have : 0 < Real.sqrt (p0 y) := Real.sqrt_pos.mpr (hp0 y)
    field_simp
  have e2 : ∀ y, Real.sqrt (p0 y) ^ 2 = p0 y := fun y => Real.sq_sqrt (hp0 y).le
  have e3 : ∀ y, (|p0 y - m y| / Real.sqrt (p0 y)) ^ 2 = p0 y - 2 * m y + m y ^ 2 / p0 y := by
    intro y
    have h := hp0 y
    rw [div_pow, sq_abs, e2]
    field_simp
    ring
  simp only [e1, e2, e3, hs0, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsm] at hCS
  have hnn : 0 ≤ ∑ y, |p0 y - m y| := Finset.sum_nonneg fun y _ => abs_nonneg _
  have hle : ∑ y, |p0 y - m y| ≤ c := by nlinarith
  linarith


lemma pair_term (ρ u u' : ℝ) (h0 : 0 < ρ) (h1 : ρ < 1) :
    ∑ x : Bool, bern (ρ + u) x * bern (ρ + u') x / bern ρ x = 1 + u * u' / (ρ * (1 - ρ)) := by
  have h1' : (0:ℝ) < 1 - ρ := by linarith
  simp only [Fintype.sum_bool, bern, if_true, Bool.false_eq_true, if_false]
  field_simp
  ring

lemma pair_chi {n T : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : Fin T → ℝ)
    (B : (Fin n → Bool) → Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ b t (p : Pair n), B b t p.1.1 p.1.2 = ρ + c t * (sgn b p.1.1 * sgn b p.1.2))
    (hB01 : ∀ b t (p : Pair n), 0 ≤ B b t p.1.1 p.1.2 ∧ B b t p.1.1 p.1.2 ≤ 1)
    (B0 : Fin T → Matrix (Fin n) (Fin n) ℝ) (hB0 : ∀ t (p : Pair n), B0 t p.1.1 p.1.2 = ρ)
    (L : ℝ) (hL : L = (∑ t, c t ^ 2) / (ρ * (1 - ρ))) (b b' : Fin n → Bool) :
    ∑ y, weight (B b) y * weight (B b') y / weight B0 y
    ≤ Real.exp (L * ((S (fun i => xor (b i) (b' i))) ^ 2 - n) / 2) := by
  have hbρ : ∀ x : Bool, 0 < bern ρ x := by intro x; unfold bern; split_ifs <;> linarith
  set F : Fin T → Pair n → Bool → ℝ := fun t p x =>
    bern (ρ + c t * (sgn b p.1.1 * sgn b p.1.2)) x *
      bern (ρ + c t * (sgn b' p.1.1 * sgn b' p.1.2)) x / bern ρ x with hF
  have hw : ∀ y, weight (B b) y * weight (B b') y / weight B0 y
      = ∏ t, ∏ p : Pair n, F t p (y t p) := by
    intro y
    unfold weight
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [hB, hB, hB0]
  rw [Finset.sum_congr rfl (fun y _ => hw y), sum_obs_prod F]
  have hfac : ∀ t (p : Pair n),
      0 ≤ ∑ x : Bool, F t p x ∧
      ∑ x : Bool, F t p x
        ≤ Real.exp (c t ^ 2 * (sgn (fun i => xor (b i) (b' i)) p.1.1 *
            sgn (fun i => xor (b i) (b' i)) p.1.2) / (ρ * (1 - ρ))) := by
    intro t p
    constructor
    · apply Finset.sum_nonneg
      intro x _
      have e1 := hB01 b t p
      have e2 := hB01 b' t p
      rw [hB] at e1 e2
      exact div_nonneg (mul_nonneg (bern_nonneg e1.1 e1.2 x) (bern_nonneg e2.1 e2.2 x))
        (hbρ x).le
    · rw [hF, pair_term ρ _ _ hρ0 hρ1, sgn_xor, sgn_xor]
      refine le_trans (le_of_eq ?_) (Real.add_one_le_exp _)
      ring
  calc ∏ t, ∏ p : Pair n, ∑ x : Bool, F t p x
      ≤ ∏ t, ∏ p : Pair n, Real.exp (c t ^ 2 * (sgn (fun i => xor (b i) (b' i)) p.1.1 *
            sgn (fun i => xor (b i) (b' i)) p.1.2) / (ρ * (1 - ρ))) := by
        apply Finset.prod_le_prod
        · intro t _; exact Finset.prod_nonneg fun p _ => (hfac t p).1
        · intro t _
          exact Finset.prod_le_prod (fun p _ => (hfac t p).1) (fun p _ => (hfac t p).2)
    _ = Real.exp (∑ t, ∑ p : Pair n, c t ^ 2 * (sgn (fun i => xor (b i) (b' i)) p.1.1 *
            sgn (fun i => xor (b i) (b' i)) p.1.2) / (ρ * (1 - ρ))) := by
        rw [Real.exp_sum]; simp only [Real.exp_sum]
    _ = Real.exp (L * ((S (fun i => xor (b i) (b' i))) ^ 2 - n) / 2) := by
        congr 1
        rw [mul_div_assoc, ← chaos_eq, hL, div_mul_eq_mul_div, Finset.sum_mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_div]

set_option maxHeartbeats 1000000 in
lemma chi_bound {n T : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : Fin T → ℝ)
    (B : (Fin n → Bool) → Fin T → Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ b t (p : Pair n), B b t p.1.1 p.1.2 = ρ + c t * (sgn b p.1.1 * sgn b p.1.2))
    (hB01 : ∀ b t (p : Pair n), 0 ≤ B b t p.1.1 p.1.2 ∧ B b t p.1.1 p.1.2 ≤ 1)
    (B0 : Fin T → Matrix (Fin n) (Fin n) ℝ) (hB0 : ∀ t (p : Pair n), B0 t p.1.1 p.1.2 = ρ)
    (L : ℝ) (hL : L = (∑ t, c t ^ 2) / (ρ * (1 - ρ))) (hL0 : 0 ≤ L)
    (hLn : 2 * L * ((n : ℝ) - 1) < 1) :
    ∑ y, (((2:ℝ) ^ n)⁻¹ * ∑ b, weight (B b) y) ^ 2 / weight B0 y
      ≤ Real.exp (L ^ 2 * n * ((n : ℝ) - 1) / (2 * (1 - 2 * L * ((n : ℝ) - 1)))) := by
  set k : ℝ := ((2:ℝ) ^ n)⁻¹ with hk
  have hρ1' : (0:ℝ) < 1 - ρ := by linarith
  have hbρ : ∀ x : Bool, 0 < bern ρ x := by intro x; unfold bern; split_ifs <;> linarith
  -- expand the square
  have hexp : ∀ y, (k * ∑ b, weight (B b) y) ^ 2 / weight B0 y
      = k ^ 2 * ∑ b, ∑ b', weight (B b) y * weight (B b') y / weight B0 y := by
    intro y
    rw [mul_pow, sq (∑ b, weight (B b) y), Finset.sum_mul_sum, mul_div_assoc, Finset.sum_div]
    simp only [Finset.sum_div]
  rw [Finset.sum_congr rfl (fun y _ => hexp y), ← Finset.mul_sum]
  have hswap : ∑ y : Obs n T, ∑ b, ∑ b', weight (B b) y * weight (B b') y / weight B0 y
      = ∑ b', ∑ b, ∑ y : Obs n T, weight (B b) y * weight (B b') y / weight B0 y := by
    calc ∑ y : Obs n T, ∑ b, ∑ b', weight (B b) y * weight (B b') y / weight B0 y
        = ∑ b, ∑ y : Obs n T, ∑ b', weight (B b) y * weight (B b') y / weight B0 y :=
          Finset.sum_comm
      _ = ∑ b, ∑ b', ∑ y : Obs n T, weight (B b) y * weight (B b') y / weight B0 y :=
          Finset.sum_congr rfl (fun b _ => Finset.sum_comm)
      _ = ∑ b', ∑ b, ∑ y : Obs n T, weight (B b) y * weight (B b') y / weight B0 y :=
          Finset.sum_comm
  rw [hswap]
  have hper := fun b b' => pair_chi ρ hρ0 hρ1 c B hB hB01 B0 hB0 L hL b b'
  have hsum : ∑ b' : Fin n → Bool, ∑ b : Fin n → Bool,
      Real.exp (L * ((S (fun i => xor (b i) (b' i))) ^ 2 - n) / 2) = 2 ^ n * G n L := by
    simp only [sum_xor _ (fun b => Real.exp (L * (S b ^ 2 - n) / 2))]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rfl
  have hk2 : k ^ 2 * (2 ^ n * 2 ^ n) = 1 := by
    rw [hk]; field_simp
  calc k ^ 2 * ∑ b', ∑ b, ∑ y, weight (B b) y * weight (B b') y / weight B0 y
      ≤ k ^ 2 * ∑ b' : Fin n → Bool, ∑ b : Fin n → Bool,
          Real.exp (L * ((S (fun i => xor (b i) (b' i))) ^ 2 - n) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
        exact Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun b _ => hper b b'
    _ = k ^ 2 * (2 ^ n * G n L) := by rw [hsum]
    _ ≤ k ^ 2 * (2 ^ n * (2 ^ n * Real.exp (L ^ 2 * n * ((n : ℝ) - 1) /
          (2 * (1 - 2 * L * ((n : ℝ) - 1)))))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact G_le n L hL0 hLn
    _ = Real.exp (L ^ 2 * n * ((n : ℝ) - 1) / (2 * (1 - 2 * L * ((n : ℝ) - 1)))) := by
        rw [← mul_assoc, ← mul_assoc, mul_assoc (k ^ 2), hk2, one_mul]

noncomputable def Jm (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun _ _ => 1

noncomputable def Θs {n : ℕ} (ρ h : ℝ) (b : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i = j then 0 else ρ + h * sgn b i * sgn b j

lemma sgn_cases {n : ℕ} (b : Fin n → Bool) (i : Fin n) : sgn b i = 1 ∨ sgn b i = -1 := by
  unfold sgn; split_ifs <;> simp

lemma abs_hss {n : ℕ} (h : ℝ) (b : Fin n → Bool) (i j : Fin n) :
    |h * sgn b i * sgn b j| = |h| := by
  rcases sgn_cases b i with hi | hi <;> rcases sgn_cases b j with hj | hj <;> simp [hi, hj]

lemma J_had {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Jm n ⊙ M = M := by
  ext i j; simp [Jm, Matrix.hadamard_apply]

lemma sum_offdiag {n : ℕ} (j : Fin n) (a : ℝ) :
    ∑ i : Fin n, (if i = j then (0:ℝ) else a) = ((n:ℝ) - 1) * a := by
  have : ∀ i : Fin n, (if i = j then (0:ℝ) else a) = a - (if i = j then a else 0) := by
    intro i; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp; ring

lemma InS_Θs {n : ℕ} (hn : 1 ≤ n) (ω ρ h : ℝ) (b : Fin n → Bool) (h1 : |h| ≤ ρ)
    (h2 : ρ + |h| ≤ 1) (h3 : ((n:ℝ) - 1) * (ρ + |h|) ≤ ω) : InS ω (Θs ρ h b) (Jm n) := by
  have hbd : ∀ i j, -|h| ≤ h * sgn b i * sgn b j ∧ h * sgn b i * sgn b j ≤ |h| := by
    intro i j
    have := abs_hss h b i j
    exact ⟨by linarith [neg_abs_le (h * sgn b i * sgn b j)],
      by linarith [le_abs_self (h * sgn b i * sgn b j)]⟩
  have hent : ∀ i j, 0 ≤ Θs ρ h b i j ∧ Θs ρ h b i j ≤ 1 := by
    intro i j
    simp only [Θs, Matrix.of_apply]
    split_ifs
    · norm_num
    · have := hbd i j
      constructor <;> linarith [this.1, this.2]
  refine ⟨⟨⟨?_, hent⟩, fun i => by simp [Θs]⟩,
    ⟨⟨?_, fun i j => by simp [Jm]⟩, fun i => by simp [Jm], fun i j => by simp [Jm]⟩, ?_⟩
  · apply Matrix.IsSymm.ext
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · simp only [Θs, Matrix.of_apply, hij, Ne.symm hij, if_false]; ring
  · apply Matrix.IsSymm.ext; intro i j; simp [Jm]
  · rw [J_had]
    unfold norm1inf
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    apply ciSup_le
    intro j
    calc ∑ i, |Θs ρ h b i j| ≤ ∑ i, (if i = j then (0:ℝ) else ρ + |h|) := by
          apply Finset.sum_le_sum; intro i _
          simp only [Θs, Matrix.of_apply]
          split_ifs
          · simp
          · rw [abs_le]
            have := hbd i j
            have : 0 ≤ |h| := abs_nonneg h
            constructor <;> linarith [(hbd i j).1, (hbd i j).2]
      _ = ((n:ℝ) - 1) * (ρ + |h|) := sum_offdiag j _
      _ ≤ ω := h3

lemma sum_fin_ite (T τ : ℕ) (hτ : τ ≤ T) (a c : ℝ) :
    ∑ t : Fin T, (if (t : ℕ) < τ then a else c) = τ * a + ((T:ℝ) - τ) * c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < τ then a else c)]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hτ
  rw [Finset.sum_range_add]
  have e1 : ∑ x ∈ Finset.range τ, (if x < τ then a else c) = ∑ x ∈ Finset.range τ, a :=
    Finset.sum_congr rfl fun x hx => if_pos (Finset.mem_range.mp hx)
  have e2 : ∑ x ∈ Finset.range m, (if τ + x < τ then a else c) = ∑ x ∈ Finset.range m, c :=
    Finset.sum_congr rfl fun x _ => if_neg (by omega)
  rw [e1, e2]; simp

lemma alt_entry {n T : ℕ} (τ : ℕ) (ρ ha hb : ℝ) (b : Fin n → Bool) (t : Fin T) (p : Pair n) :
    (altParam τ (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n)) t p.1.1 p.1.2
      = ρ + (if (t:ℕ) < τ then -hb else ha) * (sgn b p.1.1 * sgn b p.1.2) := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  unfold altParam
  split_ifs <;> simp [Jm, Θs, hne, Matrix.hadamard_apply] <;> ring

lemma null_entry {n T : ℕ} (ρ : ℝ) (b : Fin n → Bool) (t : Fin T) (p : Pair n) :
    (nullParam (T := T) (Θs ρ 0 b) (Jm n)) t p.1.1 p.1.2 = ρ := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  simp [nullParam, Jm, Θs, hne, Matrix.hadamard_apply]

lemma Θs_sub {n : ℕ} (ρ ha hb : ℝ) (b : Fin n → Bool) :
    Jm n ⊙ (Θs ρ ha b - Θs ρ (-hb) b) = sgnMat (ha + hb) b := by
  rw [J_had]
  ext i j
  simp only [Θs, sgnMat, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> ring

set_option maxHeartbeats 1000000 in
lemma param_facts (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hμ : 2 * muN n T ω α β R * ((n : ℝ) - 1) < 1)
    (h28 : muN n T ω α β R ^ 2 * n * ((n : ℝ) - 1) ≤
      2 * Ceta α β * (1 - 2 * muN n T ω α β R * ((n : ℝ) - 1)))
    :
    ∃ ρ ha hb : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ b : Fin n → Bool, InW T τ ω R (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n)) ∧
      InS ω (Θs ρ 0 (fun _ => true)) (Jm n) ∧ 0 ≤ muN n T ω α β R ∧
      muN n T ω α β R = (∑ t : Fin T, (if (t:ℕ) < τ then -hb else ha) ^ 2) / (ρ * (1 - ρ)) ∧
      Real.exp (muN n T ω α β R ^ 2 * n * ((n : ℝ) - 1) / (2 * (1 - 2 * muN n T ω α β R * ((n : ℝ) - 1))))
        ≤ 1 + (2 * (1 - (α + β))) ^ 2 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ (n:ℝ) - 1 := by linarith
  have hτR : (1:ℝ) ≤ τ := by exact_mod_cast hτ
  have hTτ : (1:ℝ) ≤ (T:ℝ) - τ := by
    have h1 : τ + 1 ≤ T := hτT
    have h2 : ((τ:ℝ) + 1) ≤ T := by exact_mod_cast h1
    linarith
  have hT0 : (0:ℝ) < T := by linarith
  set C := Ceta α β with hC
  have hη : 0 ≤ 1 - (α + β) := by linarith
  have hC0 : 0 ≤ C := Real.log_nonneg (by have := sq_nonneg (1 - (α + β)); linarith)
  have hexpC : Real.exp C = 1 + (2 * (1 - (α + β))) ^ 2 := by
    rw [hC, Ceta, Real.exp_log (by positivity)]; ring
  have hsC := Real.sqrt_nonneg (2 * C)
  have hω0 : 0 < ω := lt_of_le_of_lt hsC hω
  set ε := epsN α β ω with hεdef
  have hr4 : ((2 * C) ^ (1/4:ℝ)) ^ (2:ℕ) = Real.sqrt (2 * C) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]; norm_num
  have hε0 : 0 ≤ ε := div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _)
  have hε2 : ε ^ 2 * ω = Real.sqrt (2 * C) := by
    rw [hεdef, epsN, div_pow, Real.sq_sqrt hω0.le, hr4]; field_simp
  have hε4 : ε ^ 2 ≤ 1 / 4 := by
    have : ε ^ 2 * ω ≤ (1 / 4) * ω := by linarith
    exact le_of_mul_le_mul_right this hω0
  have hεhalf : ε ≤ 1 / 2 :=
    (sq_le_sq₀ hε0 (by norm_num)).mp (by rw [show ((1:ℝ) / 2) ^ 2 = 1 / 4 by norm_num]; exact hε4)
  set ρ := rhoTilde n α β ω with hρdef
  have hρeq : ρ * ((n:ℝ) - 1) = (1 - ε) * ω := by
    rw [hρdef, rhoTilde, ← hεdef]; field_simp
  have hρ0 : 0 < ρ := by
    have : 0 < ρ * ((n:ℝ) - 1) := by rw [hρeq]; apply mul_pos (by linarith) hω0
    exact pos_of_mul_pos_left this (by linarith)
  have hρhalf : ρ ≤ 1 / 2 := by
    have : ρ * ((n:ℝ) - 1) ≤ 1 / 2 * ((n:ℝ) - 1) := by
      rw [hρeq]; linarith [mul_nonneg hε0 hω0.le]
    exact le_of_mul_le_mul_right this (by linarith)
  have h1ρ : 1 - ρ ≠ 0 := by intro h; linarith
  have h1ε : 1 - ε ≠ 0 := by intro h; linarith
  set μ := muN n T ω α β R with hμdef
  have hden : 0 < (1 - ρ) * ((n:ℝ) - 1) * (1 - ε) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hμeq : μ * (ω * ((1 - ρ) * ((n:ℝ) - 1) * (1 - ε))) = T * R ^ 2 := by
    rw [hμdef, muN, ← hρdef, ← hεdef]; field_simp
  have hμ0 : 0 ≤ μ := by
    rw [hμdef, muN, ← hρdef, ← hεdef]
    exact mul_nonneg (by positivity) (one_div_nonneg.mpr hden.le)
  have hμs : μ * ((n:ℝ) - 1) ≤ Real.sqrt (2 * C) := by
    have h1 : (μ * ((n:ℝ) - 1)) ^ 2 ≤ 2 * C := by
      have h2 : μ ^ 2 * n * ((n:ℝ) - 1) ≤ 2 * C := by
        linarith [mul_nonneg (mul_nonneg hC0 hμ0) (by linarith : (0:ℝ) ≤ (n:ℝ) - 1)]
      linarith [mul_nonneg (sq_nonneg μ) (by linarith : (0:ℝ) ≤ (n:ℝ) - 1)]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h1)
  have hTR : (T:ℝ) * R ^ 2 ≤ (ε * ω) ^ 2 := by
    have hpe : (1 - ρ) * (1 - ε) ≤ 1 := by
      linarith [mul_nonneg hρ0.le (by linarith : (0:ℝ) ≤ 1 - ε)]
    have hm0 : 0 ≤ μ * ((n:ℝ) - 1) * ω := by
      apply mul_nonneg (mul_nonneg hμ0 (by linarith)) hω0.le
    calc (T:ℝ) * R ^ 2 = (μ * ((n:ℝ) - 1) * ω) * ((1 - ρ) * (1 - ε)) := by
          rw [← hμeq]; ring
      _ ≤ (μ * ((n:ℝ) - 1) * ω) * 1 := mul_le_mul_of_nonneg_left hpe hm0
      _ ≤ Real.sqrt (2 * C) * ω := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right hμs hω0.le
      _ = (ε * ω) ^ 2 := by rw [← hε2]; ring
  -- the change-point energy normalisation
  set qq := q ((τ:ℝ) / T) with hqdef
  have hx : 0 < (τ:ℝ) / T * (1 - τ / T) := by
    apply mul_pos (by positivity)
    rw [sub_pos, div_lt_one hT0]; linarith
  have hq2 : qq ^ 2 * (T:ℝ) ^ 2 = τ * (T - τ) := by
    rw [hqdef, q, Real.sq_sqrt hx.le]; field_simp
  have hqpos : 0 < qq := by rw [hqdef, q]; exact Real.sqrt_pos.mpr hx
  set H := R / (qq * ((n:ℝ) - 1)) with hHdef
  have hHq : H * qq * ((n:ℝ) - 1) = R := by
    rw [hHdef]; field_simp
  have hH0 : 0 < H := by rw [hHdef]; apply div_pos hR (mul_pos hqpos (by linarith))
  set ha := H * τ / T with hadef
  set hb := H * (T - τ) / T with hbdef
  have ha0 : 0 ≤ ha := by positivity
  have hb0 : 0 ≤ hb := div_nonneg (mul_nonneg hH0.le (by linarith)) hT0.le
  have hab : ha + hb = H := by rw [hadef, hbdef]; field_simp; ring
  have hXa : ((n:ℝ) - 1) * ha ≤ ε * ω := by
    have e1 : (((n:ℝ) - 1) * ha) ^ 2 * (qq ^ 2 * (T:ℝ) ^ 2) = R ^ 2 * τ ^ 2 := by
      rw [← hHq, hadef]; field_simp
    rw [hq2] at e1
    have e2 : (((n:ℝ) - 1) * ha) ^ 2 * ((T:ℝ) - τ) = R ^ 2 * τ := by
      apply mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < τ)); linear_combination e1
    have e3 : (((n:ℝ) - 1) * ha) ^ 2 ≤ (T:ℝ) * R ^ 2 := by
      have : (((n:ℝ) - 1) * ha) ^ 2 * ((T:ℝ) - τ) ≤ ((T:ℝ) * R ^ 2) * ((T:ℝ) - τ) := by
        rw [e2]
        linarith [mul_nonneg (mul_nonneg (sq_nonneg R) hT0.le) (by linarith : (0:ℝ) ≤ (T:ℝ) - τ - 1),
          mul_nonneg (sq_nonneg R) (by linarith : (0:ℝ) ≤ (T:ℝ) - τ)]
      exact le_of_mul_le_mul_right this (by linarith)
    have hX0 : 0 ≤ ((n:ℝ) - 1) * ha := mul_nonneg (by linarith) ha0
    have hY0 : 0 ≤ ε * ω := mul_nonneg hε0 hω0.le
    exact (sq_le_sq₀ hX0 hY0).mp (le_trans e3 hTR)
  have hXb : ((n:ℝ) - 1) * hb ≤ ε * ω := by
    have e1 : (((n:ℝ) - 1) * hb) ^ 2 * (qq ^ 2 * (T:ℝ) ^ 2) = R ^ 2 * ((T:ℝ) - τ) ^ 2 := by
      rw [← hHq, hbdef]; field_simp
    rw [hq2] at e1
    have e2 : (((n:ℝ) - 1) * hb) ^ 2 * τ = R ^ 2 * ((T:ℝ) - τ) := by
      apply mul_left_cancel₀ (ne_of_gt (by linarith : (0:ℝ) < (T:ℝ) - τ)); linear_combination e1
    have e3 : (((n:ℝ) - 1) * hb) ^ 2 ≤ (T:ℝ) * R ^ 2 := by
      have : (((n:ℝ) - 1) * hb) ^ 2 * τ ≤ ((T:ℝ) * R ^ 2) * τ := by
        rw [e2]
        linarith [mul_nonneg (mul_nonneg (sq_nonneg R) hT0.le) (by linarith : (0:ℝ) ≤ (τ:ℝ) - 1),
          mul_nonneg (sq_nonneg R) (by linarith : (0:ℝ) ≤ (τ:ℝ))]
      exact le_of_mul_le_mul_right this (by linarith)
    have hX0 : 0 ≤ ((n:ℝ) - 1) * hb := mul_nonneg (by linarith) hb0
    have hY0 : 0 ≤ ε * ω := mul_nonneg hε0 hω0.le
    exact (sq_le_sq₀ hX0 hY0).mp (le_trans e3 hTR)
  -- validity of the priors
  have hInS : ∀ (h : ℝ) (b : Fin n → Bool), 0 ≤ h → ((n:ℝ) - 1) * h ≤ ε * ω →
      InS ω (Θs ρ h b) (Jm n) ∧ InS ω (Θs ρ (-h) b) (Jm n) := by
    intro h b h0 hh
    have k1 : |h| ≤ ρ := by
      rw [abs_of_nonneg h0]
      have hm : 0 ≤ (1 - 2 * ε) * ω := mul_nonneg (by linarith) hω0.le
      have : h * ((n:ℝ) - 1) ≤ ρ * ((n:ℝ) - 1) := by rw [hρeq]; linarith
      exact le_of_mul_le_mul_right this (by linarith)
    have k3 : ((n:ℝ) - 1) * (ρ + |h|) ≤ ω := by
      rw [abs_of_nonneg h0]; linarith
    have k2 : ρ + |h| ≤ 1 := by
      have : (ρ + |h|) * ((n:ℝ) - 1) ≤ 1 * ((n:ℝ) - 1) := by linarith
      exact le_of_mul_le_mul_right this (by linarith)
    refine ⟨InS_Θs (by omega) ω ρ h b k1 k2 k3, ?_⟩
    rw [← abs_neg] at k1 k2 k3
    exact InS_Θs (by omega) ω ρ (-h) b k1 k2 k3
  have hInW : ∀ b : Fin n → Bool, InW T τ ω R (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n) := by
    intro b
    refine ⟨(hInS ha b ha0 hXa).1, (hInS hb b hb0 hXb).2, ?_⟩
    rw [Θs_sub, hab]
    have := opNorm_ge (by omega) H hH0.le b
    calc R = qq * (H * ((n:ℝ) - 1)) := by rw [← hHq]; ring
      _ ≤ qq * matrixOpNorm (sgnMat H b) := mul_le_mul_of_nonneg_left this hqpos.le
  have hInS0 : InS ω (Θs ρ 0 (fun _ => true)) (Jm n) := by
    have := (hInS 0 (fun _ => true) le_rfl (by simp; exact mul_nonneg hε0 hω0.le)).1
    exact this
  -- the chi-square bound
  set c : Fin T → ℝ := fun t => if (t:ℕ) < τ then -hb else ha with hcdef
  have hsumc : ∑ t, c t ^ 2 = τ * hb ^ 2 + ((T:ℝ) - τ) * ha ^ 2 := by
    rw [← sum_fin_ite T τ hτT.le]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [hcdef]; split_ifs <;> ring
  have hL : μ = (∑ t, c t ^ 2) / (ρ * (1 - ρ)) := by
    rw [hsumc, eq_div_iff (mul_pos hρ0 (by linarith)).ne']
    have f1 : (τ * hb ^ 2 + ((T:ℝ) - τ) * ha ^ 2) * T = H ^ 2 * (τ * ((T:ℝ) - τ)) := by
      rw [hadef, hbdef]; field_simp; ring
    rw [← hq2] at f1
    have f2 : (τ * hb ^ 2 + ((T:ℝ) - τ) * ha ^ 2) = H ^ 2 * qq ^ 2 * T := by
      apply mul_right_cancel₀ (ne_of_gt hT0); rw [f1]; ring
    have f3 : (τ * hb ^ 2 + ((T:ℝ) - τ) * ha ^ 2) * ((n:ℝ) - 1) ^ 2 = R ^ 2 * T := by
      rw [f2, ← hHq]; ring
    have f4 : μ * (ρ * (1 - ρ)) * ((n:ℝ) - 1) ^ 2 = T * R ^ 2 := by
      rw [← hμeq]
      have : μ * (ρ * (1 - ρ)) * ((n:ℝ) - 1) ^ 2 = μ * (ρ * ((n:ℝ) - 1)) * (1 - ρ) * ((n:ℝ) - 1) := by ring
      rw [this, hρeq]; ring
    have hn2 : (0:ℝ) < ((n:ℝ) - 1) ^ 2 := by positivity
    apply mul_right_cancel₀ (ne_of_gt hn2)
    rw [f4, f3]; ring
  have hchiC : Real.exp (μ ^ 2 * n * ((n : ℝ) - 1) / (2 * (1 - 2 * μ * ((n : ℝ) - 1))))
      ≤ 1 + (2 * (1 - (α + β))) ^ 2 := by
    rw [← hexpC, Real.exp_le_exp, div_le_iff₀ (by linarith)]
    linarith
  exact ⟨ρ, ha, hb, hρ0, by linarith, hInW, hInS0, hμ0, hL, hchiC⟩

set_option maxHeartbeats 1000000 in
lemma final_step {n T : ℕ} (τ : ℕ) (ω α β R ρ ha hb : ℝ) (ψ : Obs n T → Bool)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hβ0 : 0 ≤ 1 - (α + β))
    (hInW : ∀ b : Fin n → Bool, InW T τ ω R (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n))
    (hInS0 : InS ω (Θs ρ 0 (fun _ => true)) (Jm n)) (hψ : typeI (T := T) ω ψ ≤ α)
    (hchi : ∑ y, (((2:ℝ) ^ n)⁻¹ * ∑ b, weight (altParam τ (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n)) y) ^ 2
        / weight (nullParam (T := T) (Θs ρ 0 (fun _ => true)) (Jm n)) y
      ≤ 1 + (2 * (1 - (α + β))) ^ 2) :
    β ≤ typeII {τ} ω R ψ := by
  set B : (Fin n → Bool) → Fin T → Matrix (Fin n) (Fin n) ℝ :=
    fun b => altParam τ (Θs ρ ha b) (Θs ρ (-hb) b) (Jm n) with hBdef
  set B0 : Fin T → Matrix (Fin n) (Fin n) ℝ := nullParam (Θs ρ 0 (fun _ => true)) (Jm n) with hB0def
  have hB0 : ∀ t (p : Pair n), B0 t p.1.1 p.1.2 = ρ := fun t p => null_entry ρ _ t p
  -- the test inequality
  set k : ℝ := ((2:ℝ) ^ n)⁻¹ with hk
  have hk2 : k * 2 ^ n = 1 := by rw [hk]; field_simp
  have hp0 : ∀ y, 0 < weight B0 y := by
    intro y
    unfold weight
    apply Finset.prod_pos; intro t _
    apply Finset.prod_pos; intro p _
    rw [hB0]; unfold bern; split_ifs <;> linarith
  have hsm : ∑ y, k * ∑ b, weight (B b) y = 1 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [sum_weight, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast; exact hk2
  have htv := tv_bound (fun y => weight B0 y) (fun y => k * ∑ b, weight (B b) y)
    (fun y => ψ y = true) hp0 (sum_weight B0) hsm (2 * (1 - (α + β))) (by linarith)
    hchi
  have hP0 : ∑ y, (if ψ y = true then weight B0 y else 0) ≤ α := by
    have e : ∑ y, (if ψ y = true then weight B0 y else 0) = prob B0 (fun y => ψ y = true) := by
      unfold prob; exact Finset.sum_congr rfl (fun y _ => by split_ifs <;> rfl)
    rw [e]
    refine le_trans ?_ hψ
    exact le_csSup (bdd_typeI ω ψ) ⟨Θs ρ 0 (fun _ => true), Jm n, hInS0, rfl⟩
  have hP1 : ∑ y, (if ψ y = true then 0 else k * ∑ b, weight (B b) y)
      = k * ∑ b, prob (B b) (fun y => ψ y = false) := by
    have e : ∀ y, (if ψ y = true then 0 else k * ∑ b, weight (B b) y)
        = k * ∑ b, (if ψ y = false then weight (B b) y else 0) := by
      intro y; cases ψ y <;> simp
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold prob; exact Finset.sum_congr rfl (fun y _ => by split_ifs <;> rfl)
  have hβk : β ≤ k * ∑ b, prob (B b) (fun y => ψ y = false) := by
    rw [hP1] at htv
    linarith
  have hex : ∃ b ∈ (Finset.univ : Finset (Fin n → Bool)), β ≤ prob (B b) (fun y => ψ y = false) := by
    apply Finset.exists_le_of_sum_le Finset.univ_nonempty
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have : (2:ℝ) ^ n * (k * ∑ b, prob (B b) (fun y => ψ y = false))
        = ∑ b, prob (B b) (fun y => ψ y = false) := by
      rw [← mul_assoc, mul_comm ((2:ℝ) ^ n) k, hk2, one_mul]
    rw [← this]
    exact mul_le_mul_of_nonneg_left hβk (by positivity)
  obtain ⟨b, _, hbβ⟩ := hex
  refine le_trans hbβ ?_
  exact le_csSup (bdd_typeII {τ} ω R ψ)
    ⟨τ, Finset.mem_singleton_self τ, Θs ρ ha b, Θs ρ (-hb) b, Jm n, hInW b, rfl⟩

end CPDNW2

set_option maxHeartbeats 1000000 in
open CPDNetworks.Lower HighDimProb.RandomMatrices in
theorem solution (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hμ : 2 * muN n T ω α β R * ((n : ℝ) - 1) < 1)
    (h28 : muN n T ω α β R ^ 2 * n * ((n : ℝ) - 1) ≤
      2 * Ceta α β * (1 - 2 * muN n T ω α β R * ((n : ℝ) - 1)))
    (ψ : Obs n T → Bool) (hψ : typeI (T := T) ω ψ ≤ α) :
    β ≤ typeII {τ} ω R ψ := by
  obtain ⟨ρ, ha, hb, hρ0, hρ1, hInW, hInS0, hμ0, hL, hchiC⟩ :=
    CPDNW2.param_facts n T τ ω α β R hn hτ hτT hα hα1 hβ hβα hω hε hωn hR hμ h28
  have hchi := CPDNW2.chi_bound ρ hρ0 hρ1 (fun t => if (t:ℕ) < τ then -hb else ha)
    (fun b => altParam τ (CPDNW2.Θs ρ ha b) (CPDNW2.Θs ρ (-hb) b) (CPDNW2.Jm n))
    (fun b t p => CPDNW2.alt_entry τ ρ ha hb b t p)
    (fun b t p => by
      show 0 ≤ (altParam τ (CPDNW2.Θs ρ ha b) (CPDNW2.Θs ρ (-hb) b) (CPDNW2.Jm n)) t p.1.1 p.1.2 ∧
        (altParam τ (CPDNW2.Θs ρ ha b) (CPDNW2.Θs ρ (-hb) b) (CPDNW2.Jm n)) t p.1.1 p.1.2 ≤ 1
      unfold altParam
      split_ifs
      · exact CPDNW2.InS_entries (T := T) (hInW b).2.1 t p
      · exact CPDNW2.InS_entries (T := T) (hInW b).1 t p)
    (nullParam (T := T) (CPDNW2.Θs ρ 0 (fun _ => true)) (CPDNW2.Jm n)) (fun t p => CPDNW2.null_entry ρ _ t p)
    (muN n T ω α β R) hL hμ0 hμ
  exact CPDNW2.final_step τ ω α β R ρ ha hb ψ hρ0 hρ1 (by linarith) hInW hInS0 hψ (le_trans hchi hchiC)
