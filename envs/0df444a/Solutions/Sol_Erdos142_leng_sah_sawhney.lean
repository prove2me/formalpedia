-- Prove2me | solution 1 for Erdos142.leng_sah_sawhney
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-28T13:35:23.893999+00:00
-- url     : https://prove2.me/submissions/4b0e977f-603d-4956-9e7c-fad1b7f2aab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Definitions.Def_LSSInterface
import Theorems.Thm_LSS_structured_inverse_and_schmidt

section LSSFile_GVN



/-!
# Gowers sums on `ZMod p` and the generalised von Neumann inequality

For `f : ZMod p → ℝ` we define the normalised Gowers sums `gs d f`
(`gs 0 f = 𝔼 f`, `gs (d+1) f = 𝔼_h gs d (Δ_h f)` with `Δ_h f (x) = f x * f (x + h)`), and prove
the generalised von Neumann inequality for progressions `x + a_j y` with distinct `a_j`.
-/

open Finset

namespace LSS

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Multiplicative derivative on `ZMod p`. -/
def dm (h : ZMod p) (f : ZMod p → ℝ) : ZMod p → ℝ := fun x => f x * f (x + h)

/-- Normalised Gowers sum of order `d`. -/
def gs : ℕ → (ZMod p → ℝ) → ℝ
  | 0, f => (∑ x, f x) / p
  | d + 1, f => (∑ h, gs d (dm h f)) / p

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos

lemma sum_add_right' (F : ZMod p → ℝ) (c : ZMod p) : ∑ x, F (x + c) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

lemma sum_mul_left' (F : ZMod p → ℝ) {b : ZMod p} (hb : b ≠ 0) : ∑ h, F (b * h) = ∑ h, F h :=
  Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun _ => rfl)

lemma sum_affine (F : ZMod p → ℝ) (x : ZMod p) {b : ZMod p} (hb : b ≠ 0) :
    ∑ y, F (x + b * y) = ∑ z, F z := by
  exact (sum_mul_left' (fun z => F (x + z)) hb).trans (by simpa [add_comm] using sum_add_right' F x)

lemma gs_one (f : ZMod p → ℝ) : gs 1 f = ((∑ x, f x) / p) ^ 2 := by
  simp only [gs, dm]
  have hp := (p_pos (p := p)).ne'
  have : ∀ h : ZMod p, ∑ x, f x * f (x + h) = ∑ x, f x * f (x + h) := fun _ => rfl
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hs : ∀ y : ZMod p, ∑ i, f (y + i) = ∑ x, f x := fun y => by
    simpa [add_comm] using sum_add_right' f y
  simp_rw [hs, ← Finset.sum_mul]
  field_simp

lemma gs_nonneg : ∀ (d : ℕ), 1 ≤ d → ∀ f : ZMod p → ℝ, 0 ≤ gs d f
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, f => by rw [gs_one]; positivity
  | d + 2, _, f => by
    simp only [gs]
    have := p_pos (p := p)
    apply div_nonneg _ this.le
    apply Finset.sum_nonneg
    intro h _
    exact gs_nonneg (d + 1) (by omega) _

lemma abs_dm_le {f : ZMod p → ℝ} (hf : ∀ x, |f x| ≤ 1) (h : ZMod p) (x : ZMod p) :
    |dm h f x| ≤ 1 := by
  simp only [dm, abs_mul]
  exact mul_le_one₀ (hf x) (abs_nonneg _) (hf _)

/-- The progression average `𝔼_{x,y} ∏_j f_j (x + a_j y)`. -/
def pavg {m : ℕ} (f : Fin m → ZMod p → ℝ) (a : Fin m → ZMod p) : ℝ :=
  (∑ x, ∑ y, ∏ j, f j (x + a j * y)) / (p : ℝ) ^ 2

lemma abs_avg_le {f : ZMod p → ℝ} (hf : ∀ x, |f x| ≤ 1) : |(∑ x, f x) / p| ≤ 1 := by
  have hp := p_pos (p := p)
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  calc |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : ZMod p, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
    _ = p := by simp

/-- Shift the first coefficient to `0`. -/
lemma pavg_shift {m : ℕ} (f : Fin (m + 1) → ZMod p → ℝ) (a : Fin (m + 1) → ZMod p) :
    pavg f a = (∑ x, f 0 x * ∑ y, ∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y)) /
      (p : ℝ) ^ 2 := by
  unfold pavg
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  conv_lhs => rw [← sum_add_right' _ (-(a 0 * y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fin.prod_univ_succ]
  congr 1
  · congr 1; ring
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  ring

lemma gvn_base (f : Fin 2 → ZMod p → ℝ) (hf : ∀ j x, |f j x| ≤ 1) (a : Fin 2 → ZMod p)
    (ha : Function.Injective a) : |pavg f a| ^ 2 ≤ gs 1 (f 1) := by
  rw [pavg_shift, gs_one]
  have hb : a 1 - a 0 ≠ 0 := sub_ne_zero.mpr (fun h => by have := ha h; simp at this)
  have hsum : ∀ x, ∑ y, ∏ j : Fin 1, f j.succ (x + (a j.succ - a 0) * y) = ∑ z, f 1 z := by
    intro x
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.succ_zero_eq_one,
      Finset.prod_singleton]
    exact sum_affine (f 1) x hb
  simp_rw [hsum, ← Finset.sum_mul]
  have hp := p_pos (p := p)
  have e : (∑ x, f 0 x) * (∑ z, f 1 z) / (p : ℝ) ^ 2 =
      ((∑ x, f 0 x) / p) * ((∑ z, f 1 z) / p) := by field_simp
  rw [e, abs_mul, mul_pow, ← sq_abs ((∑ z, f 1 z) / p)]
  have h0 := abs_avg_le (hf 0)
  have : |(∑ x, f 0 x) / p| ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one, abs_abs]; exact h0
  calc |(∑ x, f 0 x) / p| ^ 2 * |(∑ z, f 1 z) / p| ^ 2
      ≤ 1 * |(∑ z, f 1 z) / p| ^ 2 := by gcongr
    _ = _ := one_mul _

/-- The key Cauchy–Schwarz step. -/
lemma pavg_sq_le {m : ℕ} (f : Fin (m + 1) → ZMod p → ℝ) (hf : ∀ j x, |f j x| ≤ 1)
    (a : Fin (m + 1) → ZMod p) :
    |pavg f a| ^ 2 ≤ (∑ h, pavg (fun j : Fin m => dm ((a j.succ - a 0) * h) (f j.succ))
      (fun j => a j.succ - a 0)) / p := by
  rw [pavg_shift]
  have hp := p_pos (p := p)
  set I : ZMod p → ℝ := fun x => ∑ y, ∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y) with hI
  have h1 : |∑ x, f 0 x * I x| ≤ ∑ x, |I x| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hf 0 x)
  have h2 : (∑ x, |I x|) ^ 2 ≤ p * ∑ x, I x ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ZMod p => (1 : ℝ))
      (fun x => |I x|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
      mul_one, sq_abs] at hcs
    exact hcs
  have h3 : ∑ x, I x ^ 2 = ∑ h, ∑ x, ∑ y,
      ∏ j : Fin m, dm ((a j.succ - a 0) * h) (f j.succ) (x + (a j.succ - a 0) * y) := by
    have hx : ∀ x, I x ^ 2 = ∑ y, ∑ h, (∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y)) *
        ∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * (h + y)) := by
      intro x
      rw [sq, hI]
      simp only [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      exact (sum_add_right' (fun y' => (∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y)) *
        ∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y')) y).symm
    set A : ZMod p → ZMod p → ZMod p → ℝ := fun x y h =>
      (∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * y)) *
        ∏ j : Fin m, f j.succ (x + (a j.succ - a 0) * (h + y)) with hA
    calc ∑ x, I x ^ 2 = ∑ x, ∑ y, ∑ h, A x y h := by simp_rw [hx]; rfl
      _ = ∑ x, ∑ h, ∑ y, A x y h := Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ h, ∑ x, ∑ y, A x y h := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x _ =>
          Finset.sum_congr rfl fun y _ => ?_
        simp only [hA, dm, Finset.prod_mul_distrib]
        congr 1
        apply Finset.prod_congr rfl
        intro j _
        congr 1
        ring
  have hlhs : |(∑ x, f 0 x * I x) / (p : ℝ) ^ 2| ^ 2 ≤ p * (∑ x, I x ^ 2) / (p : ℝ) ^ 4 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2), div_pow]
    have : |∑ x, f 0 x * I x| ^ 2 ≤ p * ∑ x, I x ^ 2 :=
      (pow_le_pow_left₀ (abs_nonneg _) h1 2).trans h2
    calc |∑ x, f 0 x * I x| ^ 2 / ((p : ℝ) ^ 2) ^ 2 ≤ p * (∑ x, I x ^ 2) / ((p : ℝ) ^ 2) ^ 2 := by
          gcongr
      _ = _ := by ring
  refine hlhs.trans (le_of_eq ?_)
  rw [h3]
  unfold pavg
  rw [← Finset.sum_div]
  field_simp

lemma pavg_bdd {m : ℕ} (f : Fin m → ZMod p → ℝ) (hf : ∀ j x, |f j x| ≤ 1)
    (a : Fin m → ZMod p) : |pavg f a| ≤ 1 := by
  unfold pavg
  have hp := p_pos (p := p)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2), div_le_one (by positivity)]
  calc |∑ x, ∑ y, ∏ j, f j (x + a j * y)| ≤ ∑ x, ∑ y, |∏ j, f j (x + a j * y)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : ZMod p, ∑ _y : ZMod p, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j _ => hf j _)
    _ = (p : ℝ) ^ 2 := by simp; ring

/-- **Generalised von Neumann inequality.** -/
theorem gvn : ∀ (m : ℕ), 1 ≤ m → ∀ (f : Fin (m + 1) → ZMod p → ℝ), (∀ j x, |f j x| ≤ 1) →
    ∀ (a : Fin (m + 1) → ZMod p), Function.Injective a →
    |pavg f a| ^ (2 ^ m) ≤ gs m (f (Fin.last m))
  | 0, h, _, _, _, _ => absurd h (by norm_num)
  | 1, _, f, hf, a, ha => by simpa using gvn_base f hf a ha
  | m + 2, _, f, hf, a, ha => by
    have hp := p_pos (p := p)
    set b : Fin (m + 2) → ZMod p := fun j => a j.succ - a 0 with hb
    have hbinj : Function.Injective b := by
      intro i j hij
      simp only [hb, sub_left_inj] at hij
      exact Fin.succ_injective _ (ha hij)
    have hbne : ∀ j, b j ≠ 0 := by
      intro j hj
      simp only [hb, sub_eq_zero] at hj
      exact Fin.succ_ne_zero j (ha hj)
    have hS := pavg_sq_le f hf a
    set S' : ZMod p → ℝ := fun h => pavg (fun j : Fin (m + 2) => dm (b j * h) (f j.succ)) b
      with hS'
    have hIH : ∀ h, |S' h| ^ (2 ^ (m + 1)) ≤ gs (m + 1) (dm (b (Fin.last _) * h)
        (f (Fin.last _).succ)) := by
      intro h
      have := gvn (m + 1) (by omega) (fun j : Fin (m + 2) => dm (b j * h) (f j.succ))
        (fun j x => abs_dm_le (hf _) _ _) b hbinj
      simpa using this
    have hS2 : |pavg f a| ^ 2 ≤ (∑ h, |S' h|) / p := by
      refine hS.trans ?_
      gcongr with h
      exact le_abs_self _
    have hpm : ((∑ h, |S' h|) / p) ^ (2 ^ (m + 1)) ≤ (∑ h, |S' h| ^ (2 ^ (m + 1))) / p := by
      have := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ : ZMod p => (1 : ℝ) / p)
        (fun h => |S' h|) (fun _ _ => by positivity)
        (by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; field_simp)
        (fun _ _ => abs_nonneg _) (2 ^ (m + 1))
      simpa [← Finset.mul_sum, div_eq_inv_mul] using this
    calc |pavg f a| ^ (2 ^ (m + 2)) = (|pavg f a| ^ 2) ^ (2 ^ (m + 1)) := by
          rw [← pow_mul]; congr 1; ring
      _ ≤ ((∑ h, |S' h|) / p) ^ (2 ^ (m + 1)) := by
          gcongr
      _ ≤ (∑ h, |S' h| ^ (2 ^ (m + 1))) / p := hpm
      _ ≤ (∑ h, gs (m + 1) (dm (b (Fin.last _) * h) (f (Fin.last _).succ))) / p := by
          gcongr with h; exact hIH h
      _ = gs (m + 2) (f (Fin.last (m + 2))) := by
          simp only [gs]
          congr 1
          rw [show (Fin.last (m + 1)).succ = Fin.last (m + 2) from Fin.succ_last _]
          exact sum_mul_left' (fun h => gs (m + 1) (dm h (f (Fin.last (m + 2))))) (hbne _)

end

end LSS

end LSSFile_GVN

section LSSFile_Transfer



/-!
# Transfer between Gowers sums on `ℤ` and on `ZMod p`

For `g` supported on `{1, …, N}` and a prime `p ≥ 2N`, the normalised Gowers sum of the
lift of `g` to `ZMod p` equals `gowersZ N d g / p^{d+1}`.
-/

open Finset

namespace LSS

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Lift of a function on `ℤ` to `ZMod p` using the representatives `0, …, p-1`. -/
def lift (p : ℕ) (g : ℤ → ℝ) : ZMod p → ℝ := fun x => g (x.val : ℤ)

lemma sum_zmod_val (F : ℤ → ℝ) : ∑ x : ZMod p, F (x.val : ℤ) = ∑ n ∈ Ico (0 : ℤ) p, F n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine Finset.sum_nbij (fun x : ZMod p => (x.val : ℤ)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    simp only [Finset.mem_Ico]
    exact ⟨by positivity, by exact_mod_cast ZMod.val_lt x⟩
  · intro x _ y _ hxy
    simp only at hxy
    exact ZMod.val_injective p (by exact_mod_cast hxy)
  · intro n hn
    simp only [Finset.coe_Ico, Set.mem_Ico] at hn
    refine ⟨(n.toNat : ZMod p), by simp, ?_⟩
    simp only
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega

lemma sum_lift {N : ℕ} {g : ℤ → ℝ} (hg : SupportedOn N g) (hN : N < p) :
    ∑ x, lift p g x = ∑ x ∈ Icc (1 : ℤ) N, g x := by
  unfold lift
  rw [sum_zmod_val]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ico]
    omega
  · intro x _ hx
    by_contra h
    have := hg x h
    simp only [Finset.mem_Icc] at hx
    exact hx this

/-- The representative of `h : ZMod p` in `(-(p - N), N)`. -/
def rep (N : ℕ) (h : ZMod p) : ℤ := if h.val < N then (h.val : ℤ) else (h.val : ℤ) - p

lemma rep_cast (N : ℕ) (h : ZMod p) : ((rep N h : ℤ) : ZMod p) = h := by
  unfold rep
  split_ifs <;> simp

lemma rep_bounds {N : ℕ} (h : ZMod p) :
    rep N h < N ∧ -(p : ℤ) ≤ rep N h ∧ (rep N h < 0 → (N : ℤ) - p ≤ rep N h) := by
  unfold rep
  have := ZMod.val_lt h
  split_ifs with h1
  · refine ⟨by omega, by omega, fun h => by omega⟩
  · refine ⟨by omega, by omega, fun h => by omega⟩

lemma supportedOn_dmul {N : ℕ} {g : ℤ → ℝ} (hg : SupportedOn N g) (h : ℤ) :
    SupportedOn N (dmul h g) := by
  intro x hx
  apply hg x
  intro h0
  apply hx
  simp [dmul, h0]

lemma dmul_eq_zero {N : ℕ} {g : ℤ → ℝ} (hg : SupportedOn N g) {h : ℤ}
    (hh : h ∉ Ioo (-(N : ℤ)) N) : dmul h g = 0 := by
  funext x
  simp only [dmul, Pi.zero_apply]
  by_contra hne
  have h1 := hg x (left_ne_zero_of_mul hne)
  have h2 := hg (x + h) (right_ne_zero_of_mul hne)
  simp only [Finset.mem_Ioo, not_and_or, not_lt] at hh
  omega

lemma gowersZ_zero_fun (N d : ℕ) : gowersZ N d 0 = 0 := by
  induction d with
  | zero => simp [gowersZ]
  | succ d ih =>
    simp only [gowersZ]
    apply Finset.sum_eq_zero
    intro h _
    have : dmul h (0 : ℤ → ℝ) = 0 := by funext x; simp [dmul]
    rw [this, ih]

lemma dm_lift {N : ℕ} {g : ℤ → ℝ} (hg : SupportedOn N g) (hp : 2 * N ≤ p) (h : ZMod p) :
    dm h (lift p g) = lift p (dmul (rep N h) g) := by
  funext x
  simp only [dm, lift, dmul]
  by_cases h0 : g (x.val : ℤ) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 1
  have hx := hg _ h0
  obtain ⟨hr2, hr1, hr3⟩ := rep_bounds (N := N) h
  set z : ℤ := (x.val : ℤ) + rep N h with hz
  have hcast : x + h = ((z : ℤ) : ZMod p) := by
    rw [hz]; push_cast; rw [rep_cast]; simp
  have hval : (((x + h).val : ℕ) : ℤ) = z % p := by
    rw [hcast, ZMod.val_intCast]
  rw [hval]
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hzlt : z < p := by omega
  by_cases hz0 : 0 ≤ z
  · rw [Int.emod_eq_of_lt hz0 hzlt]
  · -- `z` is negative, so the true value `z + p` lies outside the support
    have hzp : z % p = z + p := by
      rw [← Int.add_mul_emod_self_right z 1 p, one_mul]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hzp]
    have e1 : g (z + p) = 0 := by
      by_contra hne
      have := hg _ hne
      have := hr3 (by omega)
      omega
    have e2 : g z = 0 := by
      by_contra hne
      have := hg _ hne
      omega
    rw [e1, e2]

lemma sum_rep {N : ℕ} (hp : 2 * N ≤ p) (G : ℤ → ℝ) (hG : ∀ t, t ∉ Ioo (-(N : ℤ)) N → G t = 0) :
    ∑ h : ZMod p, G (rep N h) = ∑ t ∈ Ioo (-(N : ℤ)) N, G t := by
  have hinj : Set.InjOn (rep (p := p) N) (Finset.univ : Finset (ZMod p)) := by
    intro a _ b _ hab
    rw [← rep_cast (p := p) N a, ← rep_cast (p := p) N b, hab]
  rw [← Finset.sum_image (f := G) hinj]
  symm
  apply Finset.sum_subset
  · intro t ht
    simp only [Finset.mem_Ioo] at ht
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(t : ZMod p), ?_⟩
    have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hp' : 2 * (N : ℤ) ≤ p := by exact_mod_cast hp
    unfold rep
    by_cases ht0 : 0 ≤ t
    · have : ((t : ZMod p).val : ℤ) = t := by
        rw [ZMod.val_intCast, Int.emod_eq_of_lt ht0 (by omega)]
      rw [if_pos (by omega), this]
    · have : ((t : ZMod p).val : ℤ) = t + p := by
        rw [ZMod.val_intCast, ← Int.add_mul_emod_self_right t 1 p, one_mul]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      rw [if_neg (by omega), this]
      ring
  · intro t _ ht
    exact hG t ht

/-- **Transfer.** -/
theorem transfer {N : ℕ} (hp : 2 * N ≤ p) (hN : 0 < N) :
    ∀ (d : ℕ) (g : ℤ → ℝ), SupportedOn N g → (p : ℝ) ^ (d + 1) * gs d (lift p g) = gowersZ N d g
  | 0, g, hg => by
    simp only [gs, gowersZ, zero_add, pow_one]
    rw [sum_lift hg (by omega)]
    have := p_pos (p := p)
    field_simp
  | d + 1, g, hg => by
    simp only [gs, gowersZ]
    have hpp := p_pos (p := p)
    have e : ∀ h : ZMod p, gs d (dm h (lift p g)) =
        gowersZ N d (dmul (rep N h) g) / (p : ℝ) ^ (d + 1) := by
      intro h
      rw [dm_lift hg hp, ← transfer hp hN d _ (supportedOn_dmul hg _)]
      field_simp
    simp_rw [e]
    rw [← Finset.sum_div,
      sum_rep hp (fun t => gowersZ N d (dmul t g))
        (fun t ht => by (try simp only); rw [dmul_eq_zero hg ht, gowersZ_zero_fun])]
    field_simp
    ring

end

end LSS

end LSSFile_Transfer

section LSSFile_Lambda



/-!
# Progression counts: telescoping, `L¹` and Gowers-norm control
-/

open Finset

namespace LSS

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The hybrid family used in telescoping: `v` before position `i`, `u - v` at `i`, `u` after. -/
def mix {k : ℕ} (u v : ZMod p → ℝ) (i : Fin k) : Fin k → ZMod p → ℝ :=
  fun j => if j < i then v else if j = i then u - v else u

omit [Fact p.Prime] in
lemma prod_sub_prod_mix {k : ℕ} (u v : ZMod p → ℝ) (z : Fin k → ZMod p) :
    ∏ j, u (z j) - ∏ j, v (z j) = ∑ i, ∏ j, mix u v i j (z j) := by
  set P : ℕ → ℝ := fun i => ∏ j : Fin k, (if (j : ℕ) < i then v (z j) else u (z j)) with hP
  have h0 : P 0 = ∏ j, u (z j) := by simp [hP]
  have hk : P k = ∏ j, v (z j) := by
    simp only [hP]
    exact Finset.prod_congr rfl (fun j _ => by simp [j.isLt])
  have hstep : ∀ i : Fin k, P i - P (i + 1) = ∏ j, mix u v i j (z j) := by
    intro i
    simp only [hP]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j : Fin k => if (j : ℕ) < (i : ℕ) + 1 then v (z j) else u (z j))
        (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => mix u v i j (z j)) (Finset.mem_univ i)]
    have hrest : ∀ j ∈ (Finset.univ : Finset (Fin k)).erase i,
        (if (j : ℕ) < (i : ℕ) + 1 then v (z j) else u (z j)) =
          (if (j : ℕ) < i then v (z j) else u (z j)) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have : (j : ℕ) ≠ i := fun h => hji (Fin.ext h)
      by_cases h1 : (j : ℕ) < i
      · rw [if_pos (by omega), if_pos h1]
      · rw [if_neg (by omega), if_neg h1]
    have hrest2 : ∀ j ∈ (Finset.univ : Finset (Fin k)).erase i,
        mix u v i j (z j) = (if (j : ℕ) < i then v (z j) else u (z j)) := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      simp only [mix]
      by_cases h1 : j < i
      · rw [if_pos h1, if_pos (by exact_mod_cast h1)]
      · rw [if_neg h1, if_neg hji, if_neg (by exact_mod_cast h1)]
    rw [Finset.prod_congr rfl hrest, Finset.prod_congr rfl hrest2]
    simp only [lt_irrefl, if_false, lt_add_one, if_true, mix, Pi.sub_apply]
    ring
  rw [← h0, ← hk]
  have := Finset.sum_range_sub' P k
  rw [← this, ← Fin.sum_univ_eq_sum_range (fun i => P i - P (i + 1))]
  exact Finset.sum_congr rfl (fun i _ => hstep i)

lemma pavg_sub_mix {k : ℕ} (u v : ZMod p → ℝ) (a : Fin k → ZMod p) :
    pavg (fun _ => u) a - pavg (fun _ => v) a = ∑ i, pavg (mix u v i) a := by
  unfold pavg
  rw [← sub_div, ← Finset.sum_div]
  congr 1
  have h : ∀ x y, ∏ j, u (x + a j * y) - ∏ j, v (x + a j * y) =
      ∑ i, ∏ j, mix u v i j (x + a j * y) :=
    fun x y => prod_sub_prod_mix u v (fun j => x + a j * y)
  calc (∑ x, ∑ y, ∏ j, u (x + a j * y)) - ∑ x, ∑ y, ∏ j, v (x + a j * y)
      = ∑ x, ∑ y, (∏ j, u (x + a j * y) - ∏ j, v (x + a j * y)) := by
        simp [Finset.sum_sub_distrib]
    _ = ∑ x, ∑ y, ∑ i, ∏ j, mix u v i j (x + a j * y) := by simp_rw [h]
    _ = ∑ x, ∑ i, ∑ y, ∏ j, mix u v i j (x + a j * y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Permuting the functions together with the coefficients does not change the average. -/
lemma pavg_perm {k : ℕ} (F : Fin k → ZMod p → ℝ) (a : Fin k → ZMod p) (σ : Equiv.Perm (Fin k)) :
    pavg (fun j => F (σ j)) (fun j => a (σ j)) = pavg F a := by
  unfold pavg
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  exact Equiv.prod_comp σ (fun j => F j (x + a j * y))

/-- `L¹` control of the progression average by one function. -/
lemma abs_pavg_le_L1 {k : ℕ} (F : Fin k → ZMod p → ℝ) (a : Fin k → ZMod p) (i : Fin k) {B : ℝ}
    (hF : ∀ j, j ≠ i → ∀ x, |F j x| ≤ B) :
    |pavg F a| ≤ B ^ (k - 1) * (∑ x, |F i x|) / p := by
  unfold pavg
  have hp := p_pos (p := p)
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)]
  have key : ∀ x y, |∏ j, F j (x + a j * y)| ≤ B ^ (k - 1) * |F i (x + a i * y)| := by
    intro x y
    rw [Finset.abs_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm]
    gcongr
    calc ∏ j ∈ Finset.univ.erase i, |F j (x + a j * y)| ≤ ∏ j ∈ Finset.univ.erase i, B :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _)
            (fun j hj => hF j (Finset.ne_of_mem_erase hj) _)
      _ = B ^ (k - 1) := by simp
  have hsum : |∑ x, ∑ y, ∏ j, F j (x + a j * y)| ≤ p * (B ^ (k - 1) * ∑ x, |F i x|) := by
    calc |∑ x, ∑ y, ∏ j, F j (x + a j * y)| ≤ ∑ x, ∑ y, |∏ j, F j (x + a j * y)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, ∑ y, B ^ (k - 1) * |F i (x + a i * y)| :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => key x y
      _ = ∑ y, B ^ (k - 1) * ∑ x, |F i (x + a i * y)| := by
          rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = ∑ _y : ZMod p, B ^ (k - 1) * ∑ x, |F i x| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [sum_add_right' (fun x => |F i x|)]
      _ = p * (B ^ (k - 1) * ∑ x, |F i x|) := by simp
  rw [div_le_div_iff₀ (by positivity) hp]
  calc |∑ x, ∑ y, ∏ j, F j (x + a j * y)| * p ≤ p * (B ^ (k - 1) * ∑ x, |F i x|) * p := by
        gcongr
    _ = B ^ (k - 1) * (∑ x, |F i x|) * (p : ℝ) ^ 2 := by ring

/-- `L¹` telescoping bound. -/
lemma abs_pavg_sub_le_L1 {k : ℕ} (u v : ZMod p → ℝ) (a : Fin k → ZMod p) {B : ℝ}
    (hu : ∀ x, |u x| ≤ B) (hv : ∀ x, |v x| ≤ B) :
    |pavg (fun _ => u) a - pavg (fun _ => v) a| ≤ k * (B ^ (k - 1) * (∑ x, |u x - v x|) / p) := by
  rw [pavg_sub_mix]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin k, |pavg (mix u v i) a| ≤ B ^ (k - 1) * (∑ x, |u x - v x|) / p := by
    intro i
    have := abs_pavg_le_L1 (mix u v i) a i (by
      intro j hj x
      simp only [mix]
      split_ifs with h1
      · exact hv x
      · exact hu x)
    simpa [mix] using this
  calc ∑ i, |pavg (mix u v i) a| ≤ ∑ _i : Fin k, B ^ (k - 1) * (∑ x, |u x - v x|) / p :=
        Finset.sum_le_sum fun i _ => this i
    _ = _ := by simp

/-- Gowers-norm telescoping bound (via the generalised von Neumann inequality). -/
lemma abs_pavg_sub_le_gs {m : ℕ} (hm : 1 ≤ m) (u v : ZMod p → ℝ) (a : Fin (m + 1) → ZMod p)
    (ha : Function.Injective a) (hu : ∀ x, |u x| ≤ 1) (hv : ∀ x, |v x| ≤ 1)
    (huv : ∀ x, |u x - v x| ≤ 1) {η : ℝ} (hη : 0 ≤ η) (hg : gs m (u - v) ≤ η ^ (2 ^ m)) :
    |pavg (fun _ => u) a - pavg (fun _ => v) a| ≤ (m + 1) * η := by
  rw [pavg_sub_mix]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ i : Fin (m + 1), |pavg (mix u v i) a| ≤ η := by
    intro i
    set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i (Fin.last m) with hσ
    rw [← pavg_perm (mix u v i) a σ]
    have hF : ∀ j x, |mix u v i (σ j) x| ≤ 1 := by
      intro j x
      simp only [mix]
      split_ifs
      · exact hv x
      · exact huv x
      · exact hu x
    have hinj : Function.Injective (fun j => a (σ j)) := ha.comp σ.injective
    have h := gvn m hm (fun j => mix u v i (σ j)) hF (fun j => a (σ j)) hinj
    have hlast : mix u v i (σ (Fin.last m)) = u - v := by
      simp [hσ, mix]
    have hlast' : (fun j => mix u v i (σ j)) (Fin.last m) = u - v := hlast
    first | rw [hlast'] at h | rw [hlast] at h
    have h2 : |pavg (fun j => mix u v i (σ j)) fun j => a (σ j)| ^ (2 ^ m) ≤ η ^ (2 ^ m) :=
      h.trans hg
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) hη (by positivity)).mp h2
  calc ∑ i, |pavg (mix u v i) a| ≤ ∑ _i : Fin (m + 1), η := Finset.sum_le_sum fun i _ => this i
    _ = (m + 1) * η := by simp

end

end LSS

end LSSFile_Lambda

section LSSFile_APCount



/-!
# Counting progressions in `ZMod p`

* A progression-free `A ⊆ {1, …, N}` has only the trivial progressions modulo a prime `p ≥ 2N`.
* The interval `{1, …, N}` has `≫ N² / k` progressions of length `k`.
-/

open Finset

namespace LSS

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- Indicator function of a finite set of naturals, viewed on `ℤ`. -/
def ind (A : Finset ℕ) : ℤ → ℝ := fun x => if 0 ≤ x ∧ x.toNat ∈ A then 1 else 0

/-- The coefficients `0, 1, …, k-1` of a `k`-term progression. -/
def apc (p k : ℕ) : Fin k → ZMod p := fun j => ((j : ℕ) : ZMod p)

lemma ind_nonneg (A : Finset ℕ) (x : ℤ) : 0 ≤ ind A x := by unfold ind; split_ifs <;> norm_num

lemma ind_le_one (A : Finset ℕ) (x : ℤ) : ind A x ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma ind_eq_one {A : Finset ℕ} {x : ℤ} (h : ind A x ≠ 0) : 0 ≤ x ∧ x.toNat ∈ A := by
  unfold ind at h; split_ifs at h with h1
  · exact h1
  · exact absurd rfl h

lemma supportedOn_ind {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N) : SupportedOn N (ind A) := by
  intro x hx
  obtain ⟨h0, h1⟩ := ind_eq_one hx
  have := Finset.mem_Icc.mp (hA h1)
  omega

lemma sum_ind {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N) :
    ∑ x ∈ Icc (1 : ℤ) N, ind A x = A.card := by
  unfold ind
  rw [Finset.sum_boole]
  congr 1
  symm
  refine Finset.card_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_
  · intro n hn
    have := Finset.mem_Icc.mp (hA hn)
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, by omega, by simpa using hn⟩
  · intro a _ b _ h; (try simp only at h); exact_mod_cast h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    exact ⟨x.toNat, hx.2.2, by (try simp only); omega⟩

omit [Fact p.Prime] in
lemma lift_ind_mem {A : Finset ℕ} {z : ZMod p} (h : lift p (ind A) z ≠ 0) : z.val ∈ A := by
  have := (ind_eq_one h).2
  simpa only [Int.toNat_natCast] using this

/-- In a progression-free set, all progressions modulo `p ≥ 2N` are trivial. -/
lemma apfree_prod_zero {k N : ℕ} (hk : 2 ≤ k) (hp : 2 * N ≤ p) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hfree : ¬ Erdos142.HasAP k A) (x y : ZMod p) (hy : y ≠ 0) :
    ∏ j : Fin k, lift p (ind A) (x + apc p k j * y) = 0 := by
  by_contra hne
  have hall : ∀ j : Fin k, (x + apc p k j * y).val ∈ A := fun j =>
    lift_ind_mem (Finset.prod_ne_zero_iff.mp hne j (Finset.mem_univ _))
  set u : ℕ → ℤ := fun j => ((x + ((j : ℕ) : ZMod p) * y).val : ℤ) with hu
  have hmem : ∀ j, j < k → (u j).toNat ∈ A ∧ 1 ≤ u j ∧ u j ≤ N := by
    intro j hj
    have h := hall ⟨j, hj⟩
    simp only [apc] at h
    have hb := Finset.mem_Icc.mp (hA h)
    refine ⟨?_, ?_, ?_⟩
    · show ((x + ((j : ℕ) : ZMod p) * y).val : ℤ).toNat ∈ A
      rw [Int.toNat_natCast]; exact h
    · show (1 : ℤ) ≤ ((x + ((j : ℕ) : ZMod p) * y).val : ℤ); exact_mod_cast hb.1
    · show ((x + ((j : ℕ) : ZMod p) * y).val : ℤ) ≤ N; exact_mod_cast hb.2
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpN : 2 * (N : ℤ) ≤ p := by exact_mod_cast hp
  have hcast : ∀ j, ((u j : ℤ) : ZMod p) = x + ((j : ℕ) : ZMod p) * y := by
    intro j; simp [hu]
  have hstep : ∀ j, j + 1 < k → u (j + 1) - u j = u 1 - u 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h0 := hmem j (by omega)
      have h1 := hmem (j + 1) (by omega)
      have h2 := hmem (j + 1 + 1) (by omega)
      have hz : ((u (j + 1 + 1) + u j - 2 * u (j + 1) : ℤ) : ZMod p) = 0 := by
        push_cast
        rw [hcast, hcast, hcast]
        push_cast
        ring
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      have habs : |u (j + 1 + 1) + u j - 2 * u (j + 1)| < p := by
        rw [abs_lt]; constructor <;> omega
      have := Int.eq_zero_of_abs_lt_dvd hz habs
      rw [← ih (by omega)]
      omega
  set d : ℤ := u 1 - u 0 with hd
  have hlin : ∀ j, j < k → u j = u 0 + j * d := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have := hstep j hj
      have := ih (by omega)
      push_cast
      linarith
  have hd0 : d ≠ 0 := by
    intro h0
    apply hy
    have e : ((u 1 : ℤ) : ZMod p) = ((u 0 : ℤ) : ZMod p) := by rw [show u 1 = u 0 by omega]
    rw [hcast, hcast] at e
    simpa using e
  apply hfree
  rcases lt_or_gt_of_ne hd0 with hneg | hpos
  · refine ⟨(u (k - 1)).toNat, (-d).toNat, by omega, fun i hi => ?_⟩
    have h := (hmem (k - 1 - i) (by omega)).1
    have e1 := hlin (k - 1 - i) (by omega)
    have e2 := hlin (k - 1) (by omega)
    have hpos1 := (hmem (k - 1) (by omega)).2.1
    have hpos2 := (hmem (k - 1 - i) (by omega)).2.1
    convert h using 1
    have hc : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - i := by omega
    have hc2 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [hc] at e1
    rw [hc2] at e2
    have key : u (k - 1 - i) = u (k - 1) + i * (-d) := by rw [e1, e2]; ring
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega)]
    linarith
  · refine ⟨(u 0).toNat, d.toNat, by omega, fun i hi => ?_⟩
    have h := (hmem i hi).1
    have e := hlin i hi
    have hpos1 := (hmem 0 (by omega)).2.1
    have hpos2 := (hmem i hi).2.1
    convert h using 1
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega)]
    linarith

/-- Progression-free sets: the progression sum equals `|A|` (only trivial progressions). -/
theorem apfree_sum {k N : ℕ} (hk : 2 ≤ k) (hp : 2 * N ≤ p) {A : Finset ℕ}
    (hA : A ⊆ Icc 1 N) (hfree : ¬ Erdos142.HasAP k A) :
    ∑ x, ∑ y, ∏ j : Fin k, lift p (ind A) (x + apc p k j * y) = A.card := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hsplit : ∀ x : ZMod p, ∑ y, ∏ j : Fin k, lift p (ind A) (x + apc p k j * y) =
      lift p (ind A) x := by
    intro x
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    rw [Finset.sum_eq_zero (fun y hy => apfree_prod_zero hk hp hA hfree x y
      (Finset.ne_of_mem_erase hy)), add_zero]
    simp only [mul_zero, add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h01 : lift p (ind A) x = 0 ∨ lift p (ind A) x = 1 := by
      unfold lift ind; split_ifs <;> simp
    rcases h01 with h | h <;> rw [h]
    · exact zero_pow (by omega)
    · exact one_pow _
  simp_rw [hsplit]
  rw [sum_lift (supportedOn_ind hA) (by omega), sum_ind hA]

/-- The interval `{1, …, N}` contains many `k`-term progressions. -/
theorem interval_sum_ge {k N : ℕ} (hk : 1 ≤ k) (hN : 4 * k ≤ N) (hp : 2 * N ≤ p) :
    (N : ℝ) ^ 2 / (16 * k) ≤
      ∑ x, ∑ y, ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y) := by
  set X := N / 2 with hX
  set Y := N / (2 * k) with hY
  have hterm : ∀ x y : ZMod p, 0 ≤ ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y) :=
    fun x y => Finset.prod_nonneg (fun j _ => ind_nonneg _ _)
  -- restrict to `x ∈ [1, X]`, `y ∈ [0, Y)`
  have hsub : ∑ x ∈ (Icc 1 X).image (fun n : ℕ => (n : ZMod p)),
      ∑ y ∈ (range Y).image (fun n : ℕ => (n : ZMod p)),
        ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y) ≤
      ∑ x, ∑ y, ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y) := by
    calc _ ≤ ∑ x ∈ (Icc 1 X).image (fun n : ℕ => (n : ZMod p)),
          ∑ y, ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y) := by
          gcongr with x
          · exact fun y _ _ => hterm x y
          · exact Finset.subset_univ _
      _ ≤ _ := by
          gcongr
          · exact fun x _ _ => Finset.sum_nonneg (fun y _ => hterm x y)
          · exact Finset.subset_univ _
  have hXp : X < p := by omega
  have hYp : Y < p := by
    have : Y ≤ N := Nat.div_le_self _ _
    omega
  have hone : ∀ x ∈ Icc 1 X, ∀ y ∈ range Y,
      ∏ j : Fin k, lift p (ind (Icc 1 N)) ((x : ZMod p) + apc p k j * (y : ZMod p)) = 1 := by
    intro x hx y hy
    apply Finset.prod_eq_one
    intro j _
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_range] at hy
    have hjy : (j : ℕ) * y ≤ N - X := by
      have h1 : (j : ℕ) ≤ k - 1 := by omega
      have h2 : (k - 1) * y ≤ N - X := by
        have : k * Y ≤ N / 2 := by
          calc k * Y = k * (N / (2 * k)) := rfl
            _ ≤ N / 2 := by
              rw [Nat.le_div_iff_mul_le (by norm_num)]
              calc k * (N / (2 * k)) * 2 = (N / (2 * k)) * (2 * k) := by ring
                _ ≤ N := Nat.div_mul_le_self _ _
        have : (k - 1) * y ≤ k * Y := by
          calc (k - 1) * y ≤ k * y := Nat.mul_le_mul_right _ (by omega)
            _ ≤ k * Y := Nat.mul_le_mul_left _ hy.le
        omega
      calc (j : ℕ) * y ≤ (k - 1) * y := Nat.mul_le_mul_right _ h1
        _ ≤ N - X := h2
    have hval : ((x : ZMod p) + apc p k j * (y : ZMod p)).val = x + (j : ℕ) * y := by
      simp only [apc]
      rw [show (x : ZMod p) + ((j : ℕ) : ZMod p) * (y : ZMod p) = ((x + (j : ℕ) * y : ℕ) : ZMod p)
        by push_cast; ring]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp only [lift, ind, hval]
    rw [if_pos]
    refine ⟨by positivity, ?_⟩
    simp only [Int.toNat_natCast, Finset.mem_Icc]
    omega
  have hinjX : Set.InjOn (fun n : ℕ => (n : ZMod p)) (Icc 1 X : Finset ℕ) := by
    intro a ha b hb h
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hinjY : Set.InjOn (fun n : ℕ => (n : ZMod p)) (range Y : Finset ℕ) := by
    intro a ha b hb h
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg ZMod.val h
    simp only [ZMod.val_natCast] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  rw [Finset.sum_image hinjX] at hsub
  simp_rw [Finset.sum_image hinjY] at hsub
  rw [Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => hone x hx y hy))] at hsub
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Icc, nsmul_eq_mul, mul_one,
    add_tsub_cancel_right] at hsub
  refine le_trans ?_ hsub
  -- `X ≥ N/4` and `Y ≥ N/(4k)`
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hX4 : (N : ℝ) / 4 ≤ X := by
    have : N ≤ 2 * X + 1 := by omega
    have : (N : ℝ) ≤ 2 * X + 1 := by exact_mod_cast this
    have : (4 : ℝ) ≤ N := by
      have : 4 ≤ N := by omega
      exact_mod_cast this
    linarith
  have hY4 : (N : ℝ) / (4 * k) ≤ Y := by
    have h1 : N < (2 * k) * (Y + 1) := Nat.lt_mul_div_succ N (by omega)
    have h1' : (N : ℝ) < (2 * k) * (Y + 1) := by exact_mod_cast h1
    have h2 : (4 * k : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc (N : ℝ) ^ 2 / (16 * k) = (N / 4) * (N / (4 * k)) := by field_simp; ring
    _ ≤ X * Y := by gcongr
    _ = (X : ℝ) * Y := rfl

end

end LSS

end LSSFile_APCount

section LSSFile_Omega



/-!
# Step 1 of the density increment: a large superlevel set

If `A ⊆ {1, …, N}` of density `δ` has no `k`-term progression and `F : ℤ → [0,1]` has the same
mean as `1_A` and is Gowers-close to `1_A`, then `F > (1 + c')δ` on a set of size `≫ δ^k N`.
-/

open Finset

namespace LSS

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- `η = δ^k / (1024 k²)`: the Gowers-uniformity threshold. -/
def etaK (k : ℕ) (δ : ℝ) : ℝ := δ ^ k / (1024 * (k : ℝ) ^ 2)

/-- `c' = 1 / (8192 k²)`: the relative density increment on the superlevel set. -/
def cpK (k : ℕ) : ℝ := 1 / (8192 * (k : ℝ) ^ 2)

lemma one_add_pow_le_two {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n * x ≤ 1 / 2) : (1 + x) ^ n ≤ 2 := by
  have h1 : (1 + x) ^ n ≤ Real.exp x ^ n := pow_le_pow_left₀ (by linarith)
    (by linarith [Real.add_one_le_exp x]) n
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (n * x) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hn
  have h3 : Real.exp (1 / 2) < 2 := by
    have e : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
    nlinarith [Real.exp_pos (1 / 2)]
  linarith

omit [Fact p.Prime] in
lemma apc_injective {k : ℕ} (hk : k ≤ p) : Function.Injective (apc p k) := by
  intro i j h
  simp only [apc] at h
  have := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at this
  exact Fin.ext this

omit [Fact p.Prime] in
lemma lift_sub (g h : ℤ → ℝ) : lift p (fun x => g x - h x) = lift p g - lift p h := rfl

lemma pavg_const_smul {k : ℕ} (c : ℝ) (u : ZMod p → ℝ) (a : Fin k → ZMod p) :
    pavg (fun _ => c • u) a = c ^ k * pavg (fun _ => u) a := by
  unfold pavg
  simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- The progression count of `F` is far from that of `δ 1_{[N]}`. -/
theorem lam_sep {k N : ℕ} (hk : 3 ≤ k) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hAne : A.Nonempty)
    (hfree : ¬ Erdos142.HasAP k A) (hp1 : 2 * N < p) (hp2 : p ≤ 4 * N)
    (hN : 128 * k * ((N : ℝ) / A.card) ^ k ≤ N) (hN4 : 4 * k ≤ N)
    {F : ℤ → ℝ} (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hFs : SupportedOn N F)
    (hgow : gowersZ N (k - 1) (fun x => ind A x - F x) <
      etaK k (A.card / N) ^ (2 ^ (k - 1)) * (N : ℝ) ^ k) :
    1 / (1024 * k) * (A.card / N : ℝ) ^ k ≤
      |pavg (fun _ => lift p (fun x => (A.card / N : ℝ) * ind (Icc 1 N) x)) (apc p k) -
        pavg (fun _ => lift p F) (apc p k)| := by
  classical
  set δ : ℝ := A.card / N with hδ
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hAN : (A.card : ℝ) ≤ N := by
    have := Finset.card_le_card hA; simp at this; exact_mod_cast this
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hNr]; exact hAN
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hp0 : (0 : ℝ) < p := p_pos
  have hp1r : 2 * (N : ℝ) < p := by exact_mod_cast hp1
  have hp2r : (p : ℝ) ≤ 4 * N := by exact_mod_cast hp2
  set a := apc p k with ha
  have hainj : Function.Injective a := apc_injective (by omega)
  set Λ : (ZMod p → ℝ) → ℝ := fun u => pavg (fun _ => u) a with hΛ
  set fp := lift p (ind A) with hfp
  set Fp := lift p F with hFp
  -- (2) the progression count of `A`
  have hΛf : Λ fp = A.card / (p : ℝ) ^ 2 := by
    simp only [hΛ, pavg, hfp, ha]
    rw [apfree_sum (by omega) (by omega) hA hfree]
  -- (3) the progression count of `δ 1_{[N]}`
  set dp := lift p (fun x => δ * ind (Icc 1 N) x) with hdp
  have hΛd : δ ^ k / (256 * k) ≤ Λ dp := by
    have e : dp = δ • lift p (ind (Icc 1 N)) := rfl
    simp only [hΛ, e, pavg_const_smul]
    have h := interval_sum_ge (p := p) (k := k) (N := N) (by omega) hN4 (by omega)
    simp only [pavg]
    rw [mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hp2' : (p : ℝ) ^ 2 ≤ 16 * (N : ℝ) ^ 2 := by nlinarith
    have hδk : 0 ≤ δ ^ k := by positivity
    calc δ ^ k * (p : ℝ) ^ 2 ≤ δ ^ k * (16 * (N : ℝ) ^ 2) := by gcongr
      _ = δ ^ k * ((N : ℝ) ^ 2 / (16 * k)) * (256 * k) := by field_simp; norm_num
      _ ≤ δ ^ k * (∑ x, ∑ y, ∏ j : Fin k, lift p (ind (Icc 1 N)) (x + apc p k j * y)) *
          (256 * k) := by gcongr
  -- (4) Gowers control
  set η := etaK k δ with hη
  have hη0 : 0 ≤ η := by rw [hη, etaK]; positivity
  have hgs : gs (k - 1) (fp - Fp) ≤ η ^ (2 ^ (k - 1)) := by
    have ht := transfer (p := p) (by omega) hNpos (k - 1) (fun x => ind A x - F x) (by
      intro x hx
      by_contra hc
      apply hx
      have e1 : ind A x = 0 := by by_contra h; exact hc (supportedOn_ind hA x h)
      have e2 : F x = 0 := by by_contra h; exact hc (hFs x h)
      simp [e1, e2])
    rw [lift_sub] at ht
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at ht
    have : (p : ℝ) ^ k * gs (k - 1) (fp - Fp) < η ^ (2 ^ (k - 1)) * (p : ℝ) ^ k := by
      rw [ht]
      calc _ < η ^ (2 ^ (k - 1)) * (N : ℝ) ^ k := hgow
        _ ≤ η ^ (2 ^ (k - 1)) * (p : ℝ) ^ k := by
            gcongr; linarith
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    nlinarith
  have hΛfF : |Λ fp - Λ Fp| ≤ k * η := by
    have hk1 : k - 1 + 1 = k := by omega
    have h := abs_pavg_sub_le_gs (p := p) (m := k - 1) (by omega) fp Fp
      (fun j => a (Fin.cast hk1 j)) (hainj.comp (Fin.cast_injective hk1))
      (fun x => by
        simp only [hfp, lift]
        rw [abs_of_nonneg (ind_nonneg _ _)]; exact ind_le_one _ _)
      (fun x => by simp only [hFp, lift]; rw [abs_of_nonneg (hF _).1]; exact (hF _).2)
      (fun x => by
        simp only [hfp, hFp, lift]
        have := ind_nonneg A (x.val : ℤ); have := ind_le_one A (x.val : ℤ)
        have := hF (x.val : ℤ)
        rw [abs_le]; constructor <;> linarith)
      hη0 hgs
    have e : ∀ u : ZMod p → ℝ, pavg (fun _ : Fin (k - 1 + 1) => u) (fun j => a (Fin.cast hk1 j)) =
        Λ u := by
      intro u
      simp only [hΛ, pavg]
      congr 1
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      exact Fintype.prod_equiv (finCongr hk1) _ _ (fun j => rfl)
    rw [e, e] at h
    have : ((k - 1 : ℕ) : ℝ) + 1 = k := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this] at h
    exact h
  -- (5) `Λ(F)` is far from `Λ(δ 1)`
  set c : ℝ := 1 / (1024 * k) with hc
  have hsep : c * δ ^ k ≤ |Λ dp - Λ Fp| := by
    have hAp : (A.card : ℝ) / (p : ℝ) ^ 2 ≤ δ ^ k / (512 * k) := by
      have h1 : (A.card : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (4 * N) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have h2 : 1 / (4 * (N : ℝ)) ≤ δ ^ k / (512 * k) := by
        have : (N : ℝ) / A.card = 1 / δ := by rw [hδ]; field_simp
        rw [this, div_pow, one_pow] at hN
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 4 * δ ^ k)
        have e : 4 * δ ^ k * (128 * k * (1 / δ ^ k)) = 512 * k := by field_simp; ring
        nlinarith
      linarith
    have hηk : k * η = δ ^ k / (1024 * k) := by rw [hη, etaK]; field_simp
    rw [abs_sub_comm] at hΛfF
    have := abs_sub_abs_le_abs_sub (Λ dp - Λ fp) (Λ Fp - Λ fp)
    rw [show Λ dp - Λ fp - (Λ Fp - Λ fp) = Λ dp - Λ Fp by ring] at this
    have h3 : Λ dp - Λ fp ≥ δ ^ k / (256 * k) - δ ^ k / (512 * k) := by rw [hΛf]; linarith
    have h4 : δ ^ k / (256 * k) - δ ^ k / (512 * k) - δ ^ k / (1024 * k) = c * δ ^ k := by
      rw [hc]; field_simp; ring
    rw [abs_sub_comm (Λ Fp)] at hΛfF
    have h5 : |Λ Fp - Λ fp| ≤ k * η := by rw [abs_sub_comm]; exact hΛfF
    have h6 : Λ dp - Λ fp ≤ |Λ dp - Λ fp| := le_abs_self _
    linarith
  exact hsep

/-- Sum of `|F - δ|` when `F` has mean `δ`. -/
lemma sum_abs_sub_mean {N : ℕ} {F : ℤ → ℝ} {δ : ℝ} (hsum : ∑ x ∈ Icc (1 : ℤ) N, F x = δ * N) :
    ∑ x ∈ Icc (1 : ℤ) N, |F x - δ| = 2 * ∑ x ∈ Icc (1 : ℤ) N, max (F x - δ) 0 := by
  have e : ∀ x, |F x - δ| = 2 * max (F x - δ) 0 - (F x - δ) := by
    intro x
    rcases le_total 0 (F x - δ) with h | h
    · rw [abs_of_nonneg h, max_eq_left h]; ring
    · rw [abs_of_nonpos h, max_eq_right h]; ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hsum, Finset.sum_const,
    Int.card_Icc, add_sub_cancel_right, Int.toNat_natCast, nsmul_eq_mul]
  ring

/-- The final numerical step of Step 1. -/
lemma omega_numeric {c k ω d δ D cp N p : ℝ} (hc : 0 < c) (hk : 0 < k) (hω : 0 ≤ ω)
    (hD0 : 0 ≤ D) (hd : d ≤ 1) (hdδ : d * δ = D) (hN : 0 < N) (hp : 2 * N < p)
    (hcp : 4 * k * cp = c / 2)
    (hmain : c * D ≤ k * ω / p + k * (2 * d * (3 * ω + 2 * cp * δ * N) / p)) :
    c / (5 * k) * D * N ≤ ω := by
  have hp0 : 0 < p := by linarith
  have e : (k * ω / p + k * (2 * d * (3 * ω + 2 * cp * δ * N) / p)) * p =
      k * ω + 6 * k * d * ω + (4 * k * cp) * (d * δ) * N := by
    field_simp; ring
  have h1 := mul_le_mul_of_nonneg_right hmain hp0.le
  rw [e, hcp, hdδ] at h1
  have h2 : 6 * k * d * ω ≤ 6 * k * ω := by
    have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 6 * k * ω)
    linarith
  have h3 : 2 * c * D * N ≤ c * D * p := by
    have : 0 ≤ c * D := by positivity
    nlinarith
  have h4 : 3 / 2 * (c * D * N) ≤ 7 * k * ω := by nlinarith
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- **Step 1.** -/
theorem omega_large {k N : ℕ} (hk : 3 ≤ k) {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hAne : A.Nonempty)
    (hfree : ¬ Erdos142.HasAP k A) (hp1 : 2 * N < p) (hp2 : p ≤ 4 * N)
    (hN : 128 * k * ((N : ℝ) / A.card) ^ k ≤ N) (hN4 : 4 * k ≤ N)
    {F : ℤ → ℝ} (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hFs : SupportedOn N F)
    (hsum : ∑ x ∈ Icc (1 : ℤ) N, F x = A.card)
    (hgow : gowersZ N (k - 1) (fun x => ind A x - F x) <
      etaK k (A.card / N) ^ (2 ^ (k - 1)) * (N : ℝ) ^ k) :
    ((A.card / N : ℝ) ^ k / (5120 * (k : ℝ) ^ 2)) * N ≤
      (((Icc (1 : ℤ) N).filter (fun x => (1 + cpK k) * (A.card / N) < F x)).card : ℝ) := by
  classical
  have hsep := lam_sep hk hA hAne hfree hp1 hp2 hN hN4 hF hFs hgow
  set δ : ℝ := A.card / N with hδ
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hAN : (A.card : ℝ) ≤ N := by
    have := Finset.card_le_card hA; simp at this; exact_mod_cast this
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hNr]; exact hAN
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hp0 : (0 : ℝ) < p := p_pos
  have hp1r : 2 * (N : ℝ) < p := by exact_mod_cast hp1
  set a := apc p k with ha
  set Λ : (ZMod p → ℝ) → ℝ := fun u => pavg (fun _ => u) a with hΛ
  set Fp := lift p F with hFp
  set dp := lift p (fun x => δ * ind (Icc 1 N) x) with hdp
  set c : ℝ := 1 / (1024 * k) with hc
  have hsum' : ∑ x ∈ Icc (1 : ℤ) N, F x = δ * N := by rw [hsum, hδ]; field_simp
  -- (6) truncation
  set cp := cpK k with hcp
  set B : ℝ := (1 + cp) * δ with hB
  set g : ℤ → ℝ := fun x => min (F x) B with hg
  set Ω := (Icc (1 : ℤ) N).filter (fun x => B < F x) with hΩ
  set ω : ℝ := (Ω.card : ℝ) with hω
  have hcp0 : 0 < cp := by rw [hcp, cpK]; positivity
  have hB0 : 0 < B := by positivity
  have hgp : ∀ x, 0 ≤ g x := fun x => le_min (hF x).1 hB0.le
  have hFg : ∀ x, 0 ≤ F x - g x ∧ F x - g x ≤ 1 := by
    intro x; simp only [hg]
    constructor
    · linarith [min_le_left (F x) B]
    · linarith [(hF x).2, le_min (hF x).1 hB0.le]
  have hsuppFg : SupportedOn N (fun x => |F x - g x|) := by
    intro x hx
    by_contra hc'
    apply hx
    have : F x = 0 := by by_contra h; exact hc' (hFs x h)
    simp [hg, this, min_eq_left hB0.le]
  have hsum1 : ∑ x ∈ Icc (1 : ℤ) N, |F x - g x| ≤ ω := by
    rw [hω, Finset.card_eq_sum_ones, Nat.cast_sum, hΩ, Finset.sum_filter]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with h
    · rw [abs_of_nonneg (hFg x).1]; push_cast; exact (hFg x).2
    · have : g x = F x := by simp only [hg]; exact min_eq_left (not_lt.mp h)
      simp [this]
  -- sum of `(F - δ)_+`
  have hpos : ∑ x ∈ Icc (1 : ℤ) N, max (F x - δ) 0 ≤ cp * δ * N + ω := by
    rw [hω, Finset.card_eq_sum_ones, Nat.cast_sum, hΩ, Finset.sum_filter]
    have : ∀ x ∈ Icc (1 : ℤ) N, max (F x - δ) 0 ≤ cp * δ + (if B < F x then ((1 : ℕ) : ℝ) else 0) := by
      intro x _
      split_ifs with h
      · have := (hF x).2; push_cast
        have : max (F x - δ) 0 ≤ 1 := max_le (by linarith) zero_le_one
        linarith [mul_pos hcp0 hδ0]
      · push_neg at h
        simp only [add_zero]
        apply max_le _ (by positivity)
        linarith [hB]
    calc _ ≤ ∑ x ∈ Icc (1 : ℤ) N, (cp * δ + (if B < F x then ((1 : ℕ) : ℝ) else 0)) :=
          Finset.sum_le_sum this
      _ = cp * δ * N + ∑ x ∈ Icc (1 : ℤ) N, (if B < F x then ((1 : ℕ) : ℝ) else 0) := by
          rw [Finset.sum_add_distrib]; simp; ring
  have habs := sum_abs_sub_mean hsum'
  have hsum2 : ∑ x ∈ Icc (1 : ℤ) N, |δ * ind (Icc 1 N) x - g x| ≤ 3 * ω + 2 * cp * δ * N := by
    have e : ∀ x ∈ Icc (1 : ℤ) N, ind (Icc 1 N) x = 1 := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      simp only [ind]
      rw [if_pos]
      exact ⟨by omega, by simp only [Finset.mem_Icc]; omega⟩
    calc ∑ x ∈ Icc (1 : ℤ) N, |δ * ind (Icc 1 N) x - g x|
        = ∑ x ∈ Icc (1 : ℤ) N, |(F x - g x) - (F x - δ)| := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [e x hx, mul_one]; congr 1; ring
      _ ≤ ∑ x ∈ Icc (1 : ℤ) N, (|F x - g x| + |F x - δ|) :=
          Finset.sum_le_sum fun x _ => abs_sub _ _
      _ ≤ 3 * ω + 2 * cp * δ * N := by
          rw [Finset.sum_add_distrib, habs]; linarith
  -- (7) the two `L¹` telescoping estimates
  set gp := lift p g with hgpdef
  have hL1a : |Λ Fp - Λ gp| ≤ k * (1 * ω / p) := by
    have h := abs_pavg_sub_le_L1 (p := p) Fp gp a (B := 1)
      (fun x => by simp only [hFp, lift]; rw [abs_of_nonneg (hF _).1]; exact (hF _).2)
      (fun x => by
        simp only [hgpdef, lift]; rw [abs_of_nonneg (hgp _)]
        exact (min_le_left _ _).trans (hF _).2)
    rw [one_pow] at h
    have hs : ∑ x, |Fp x - gp x| = ∑ x ∈ Icc (1 : ℤ) N, |F x - g x| :=
      sum_lift hsuppFg (by omega)
    rw [hs] at h
    refine h.trans ?_
    gcongr
  have hBk : B ^ (k - 1) ≤ 2 * δ ^ (k - 1) := by
    rw [hB, mul_pow]
    have : (1 + cp) ^ (k - 1) ≤ 2 := one_add_pow_le_two hcp0.le (by
      rw [hcp, cpK]
      have : ((k - 1 : ℕ) : ℝ) ≤ k := by
        rw [Nat.cast_sub (by omega)]; push_cast; linarith
      calc ((k - 1 : ℕ) : ℝ) * (1 / (8192 * (k : ℝ) ^ 2))
          ≤ (k : ℝ) * (1 / (8192 * (k : ℝ) ^ 2)) := by gcongr
        _ = 1 / (8192 * (k : ℝ)) := by field_simp
        _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    have : 0 ≤ δ ^ (k - 1) := by positivity
    nlinarith
  have hL1b : |Λ dp - Λ gp| ≤ k * (2 * δ ^ (k - 1) * (3 * ω + 2 * cp * δ * N) / p) := by
    have hsupp : SupportedOn N (fun x => |δ * ind (Icc 1 N) x - g x|) := by
      intro x hx
      by_contra hc'
      apply hx
      have h1 : ind (Icc 1 N) x = 0 := by
        by_contra h; exact hc' (supportedOn_ind (subset_refl _) x h)
      have h2 : F x = 0 := by by_contra h; exact hc' (hFs x h)
      simp [hg, h1, h2, min_eq_left hB0.le]
    have h := abs_pavg_sub_le_L1 (p := p) dp gp a (B := B)
      (fun x => by
        simp only [hdp, lift]
        rw [abs_of_nonneg (mul_nonneg hδ0.le (ind_nonneg _ _))]
        have h1 := ind_le_one (Icc 1 N) (x.val : ℤ)
        have h2 : δ ≤ B := by rw [hB]; exact le_mul_of_one_le_left hδ0.le (by linarith)
        calc δ * ind (Icc 1 N) (x.val : ℤ) ≤ δ * 1 := mul_le_mul_of_nonneg_left h1 hδ0.le
          _ ≤ B := by rw [mul_one]; exact h2)
      (fun x => by
        simp only [hgpdef, lift]; rw [abs_of_nonneg (hgp _)]; exact min_le_right _ _)
    have hs : ∑ x, |dp x - gp x| = ∑ x ∈ Icc (1 : ℤ) N, |δ * ind (Icc 1 N) x - g x| :=
      sum_lift hsupp (by omega)
    rw [hs] at h
    refine h.trans ?_
    gcongr
  -- (8) combine
  have hω0 : 0 ≤ ω := by positivity
  have hdk : δ ^ (k - 1) ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hdk' : δ ^ (k - 1) * δ = δ ^ k := by
    rw [← pow_succ]; congr 1; omega
  have hmain : c * δ ^ k ≤ k * ω / p + k * (2 * δ ^ (k - 1) * (3 * ω + 2 * cp * δ * N) / p) := by
    have := abs_sub_le (Λ dp) (Λ gp) (Λ Fp)
    rw [abs_sub_comm (Λ gp)] at this
    have hsep' : c * δ ^ k ≤ |Λ dp - Λ Fp| := hsep
    have e1 : k * (1 * ω / p) = k * ω / p := by ring
    rw [e1] at hL1a
    linarith [hL1a, hL1b, hsep']
  have hcp' : 4 * k * cp = c / 2 := by rw [hcp, cpK, hc]; field_simp; ring
  have hc5 : δ ^ k / (5120 * (k : ℝ) ^ 2) = c / (5 * k) * δ ^ k := by rw [hc]; field_simp; ring
  rw [hc5]
  have hc0 : 0 < c := by rw [hc]; positivity
  have hD0 : 0 ≤ δ ^ k := pow_nonneg hδ0.le _
  have hfinal := omega_numeric (c := c) (k := k) (ω := ω) (d := δ ^ (k - 1)) (δ := δ) (D := δ ^ k)
    (cp := cp) (N := N) (p := p) hc0 hk0 hω0 hD0 hdk hdk' hNr hp1r hcp' hmain
  exact hfinal

end

end LSS

end LSSFile_Omega

section LSSFile_Pieces



/-!
# Step 2 of the density increment: pigeonholing over the pieces of a partition
-/

open Finset

namespace LSS

noncomputable section

lemma apSet_card (a : ℤ) {d : ℕ} (hd : 0 < d) (len : ℕ) : (apSet a d len).card = len := by
  unfold apSet
  rw [Finset.card_image_of_injective _ (fun i j h => by
    have : (d : ℤ) * i = d * j := by linarith
    have := mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) this
    exact_mod_cast this), Finset.card_range]

lemma APPart.card_piece {N : ℕ} (P : APPart N) (j : Fin P.L) : (P.piece j).card = P.len j :=
  apSet_card _ (P.hd j) _

lemma APPart.piece_subset {N : ℕ} (P : APPart N) (j : Fin P.L) : P.piece j ⊆ Icc (1 : ℤ) N :=
  fun x hx => (P.cover x).mpr ⟨j, hx⟩

lemma APPart.exists_piece {N : ℕ} (P : APPart N) {x : ℤ} (hx : x ∈ Icc (1 : ℤ) N) :
    ∃ j, x ∈ P.piece j := (P.cover x).mp hx

lemma APPart.pairwise_disjoint {N : ℕ} (P : APPart N) (s : Finset (Fin P.L)) :
    (s : Set (Fin P.L)).PairwiseDisjoint P.piece :=
  fun i _ j _ hij => P.disj i j hij

open Classical in
/-- **Pigeonhole over pieces.** If `f ∈ [0,1]` has density at least `μ` on `Ω`, and all pieces
meeting `Ω` without being contained in it lie in a small set `Bad`, then some long piece contained
in `Ω` has density at least `μ'`. -/
theorem piece_increment {N : ℕ} (P : APPart N) (f : ℤ → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) (Ω Bad : Finset ℤ) (hΩ : Ω ⊆ Icc (1 : ℤ) N) (N' μ μ' β : ℝ)
    (hN' : 0 ≤ N') (hμ' : 0 < μ') (hΩne : Ω.Nonempty)
    (hsumΩ : μ * Ω.card ≤ ∑ x ∈ Ω, f x)
    (hcross : ∀ j, (∃ x ∈ P.piece j, x ∈ Ω) → ¬ P.piece j ⊆ Ω → P.piece j ⊆ Bad)
    (hsmall : (Bad.card : ℝ) + P.L * N' ≤ β) (hβ : β ≤ (μ - μ') * Ω.card) :
    ∃ j, N' ≤ P.len j ∧ P.piece j ⊆ Ω ∧ μ' * P.len j ≤ ∑ x ∈ P.piece j, f x := by
  set G := (Finset.univ : Finset (Fin P.L)).filter (fun j => P.piece j ⊆ Ω ∧ N' ≤ P.len j) with hG
  set S := (Finset.univ : Finset (Fin P.L)).filter (fun j => (P.len j : ℝ) < N') with hS
  set Ωs := G.biUnion P.piece with hΩs
  set Sh := S.biUnion P.piece with hSh
  -- `Ω ⊆ Ω* ∪ Bad ∪ short pieces`
  have hcov : Ω ⊆ Ωs ∪ Bad ∪ Sh := by
    intro x hx
    obtain ⟨j, hj⟩ := P.exists_piece (hΩ hx)
    by_cases hsub : P.piece j ⊆ Ω
    · by_cases hlen : N' ≤ P.len j
      · apply Finset.mem_union_left; apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨j, by simp [hG, hsub, hlen], hj⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨j, by simp [hS]; linarith [not_le.mp hlen], hj⟩
    · apply Finset.mem_union_left; apply Finset.mem_union_right
      exact hcross j ⟨x, hj, hx⟩ hsub hj
  have hΩsΩ : Ωs ⊆ Ω := by
    intro x hx
    obtain ⟨j, hjG, hxj⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hjG).2.1 hxj
  -- size of the short part
  have hShcard : (Sh.card : ℝ) ≤ P.L * N' := by
    have h1 : Sh.card ≤ ∑ j ∈ S, (P.piece j).card := Finset.card_biUnion_le
    have h2 : (∑ j ∈ S, ((P.piece j).card : ℝ)) ≤ ∑ _j ∈ S, N' := by
      refine Finset.sum_le_sum fun j hj => ?_
      rw [P.card_piece]; exact (Finset.mem_filter.mp hj).2.le
    have h3 : (∑ _j ∈ S, N') ≤ P.L * N' := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have : (S.card : ℝ) ≤ P.L := by
        have := Finset.card_le_univ S; simp at this; exact_mod_cast this
      exact mul_le_mul_of_nonneg_right this hN'
    have : (Sh.card : ℝ) ≤ ∑ j ∈ S, ((P.piece j).card : ℝ) := by exact_mod_cast h1
    linarith
  -- the sum over `Ω \ Ωs` is small
  have hdiff : ∑ x ∈ Ω, f x - ∑ x ∈ Ωs, f x ≤ β := by
    rw [← Finset.sum_sdiff hΩsΩ, add_sub_cancel_right]
    have hsub : Ω \ Ωs ⊆ Bad ∪ Sh := by
      intro x hx
      obtain ⟨hxΩ, hxs⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_union.mp (hcov hxΩ) with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd h hxs
        · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ h
    calc ∑ x ∈ Ω \ Ωs, f x ≤ ∑ _x ∈ Ω \ Ωs, (1 : ℝ) := Finset.sum_le_sum fun x _ => hf1 x
      _ = ((Ω \ Ωs).card : ℝ) := by simp
      _ ≤ ((Bad ∪ Sh).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ (Bad.card : ℝ) + Sh.card := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ β := by linarith
  have hΩspos : μ' * Ω.card ≤ ∑ x ∈ Ωs, f x := by nlinarith
  have hΩs2 : μ' * Ωs.card ≤ ∑ x ∈ Ωs, f x := by
    have : (Ωs.card : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_le_card hΩsΩ
    nlinarith
  -- pigeonhole
  by_contra hcon
  push_neg at hcon
  have hdisj := P.pairwise_disjoint G
  have hsum : ∑ x ∈ Ωs, f x = ∑ j ∈ G, ∑ x ∈ P.piece j, f x := Finset.sum_biUnion hdisj
  have hcard : (Ωs.card : ℝ) = ∑ j ∈ G, (P.len j : ℝ) := by
    rw [hΩs, Finset.card_biUnion hdisj]; push_cast
    exact Finset.sum_congr rfl fun j _ => by rw [P.card_piece]
  have hGne : G.Nonempty := by
    by_contra hG0
    rw [Finset.not_nonempty_iff_eq_empty] at hG0
    have : Ωs = ∅ := by rw [hΩs, hG0, Finset.biUnion_empty]
    rw [this, Finset.sum_empty] at hΩspos
    have : (0 : ℝ) < Ω.card := by exact_mod_cast hΩne.card_pos
    nlinarith
  have hlt : ∑ j ∈ G, ∑ x ∈ P.piece j, f x < ∑ j ∈ G, μ' * P.len j := by
    apply Finset.sum_lt_sum_of_nonempty hGne
    intro j hj
    obtain ⟨hsub, hlen⟩ := (Finset.mem_filter.mp hj).2
    exact hcon j hlen hsub
  rw [← Finset.mul_sum, ← hcard, ← hsum] at hlt
  linarith

end

end LSS

end LSSFile_Pieces

section LSSFile_CondE



/-!
# Conditional expectation with respect to a labelling of `{1, …, N}`

A labelling `lab : ℤ → β` induces the partition of `{1, …, N}` into the level sets of `lab`
(a "factor"). `condE N lab f` averages `f` over these cells.
-/

open Finset

namespace LSS

noncomputable section

variable {β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-- The cell of `x`: all points of `{1, …, N}` with the same label as `x`. -/
def cell (N : ℕ) (lab : ℤ → β) (x : ℤ) : Finset ℤ := (Icc (1 : ℤ) N).filter (fun y => lab y = lab x)

/-- Conditional expectation (zero outside `{1, …, N}`). -/
def condE (N : ℕ) (lab : ℤ → β) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  if x ∈ Icc (1 : ℤ) N then (∑ y ∈ cell N lab x, f y) / (cell N lab x).card else 0

/-- The energy `∑ (𝔼(f | lab))²`. -/
def energy (N : ℕ) (lab : ℤ → β) (f : ℤ → ℝ) : ℝ := ∑ x ∈ Icc (1 : ℤ) N, condE N lab f x ^ 2

/-- `ψ` is constant on the cells of `lab`. -/
def Meas (N : ℕ) (lab : ℤ → β) (ψ : ℤ → ℝ) : Prop :=
  ∀ x ∈ Icc (1 : ℤ) N, ∀ y ∈ Icc (1 : ℤ) N, lab x = lab y → ψ x = ψ y

/-- `lab'` refines `lab`. -/
def Refines (N : ℕ) (lab' : ℤ → γ) (lab : ℤ → β) : Prop :=
  ∀ x ∈ Icc (1 : ℤ) N, ∀ y ∈ Icc (1 : ℤ) N, lab' x = lab' y → lab x = lab y

lemma mem_cell_self {N : ℕ} {lab : ℤ → β} {x : ℤ} (hx : x ∈ Icc (1 : ℤ) N) : x ∈ cell N lab x := by
  simp [cell, hx]

lemma cell_card_pos {N : ℕ} {lab : ℤ → β} {x : ℤ} (hx : x ∈ Icc (1 : ℤ) N) :
    (0 : ℝ) < (cell N lab x).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨x, mem_cell_self hx⟩

lemma cell_eq {N : ℕ} {lab : ℤ → β} {x y : ℤ} (h : lab x = lab y) : cell N lab x = cell N lab y := by
  simp [cell, h]

lemma condE_meas (N : ℕ) (lab : ℤ → β) (f : ℤ → ℝ) : Meas N lab (condE N lab f) := by
  intro x hx y hy h
  simp only [condE, if_pos hx, if_pos hy, cell_eq (N := N) h]

omit [DecidableEq β] [DecidableEq γ] in
lemma Meas.mono {N : ℕ} {lab' : ℤ → γ} {lab : ℤ → β} (hr : Refines N lab' lab) {ψ : ℤ → ℝ}
    (hψ : Meas N lab ψ) : Meas N lab' ψ :=
  fun x hx y hy h => hψ x hx y hy (hr x hx y hy h)

lemma supportedOn_condE (N : ℕ) (lab : ℤ → β) (f : ℤ → ℝ) : SupportedOn N (condE N lab f) := by
  intro x hx
  unfold condE at hx
  split_ifs at hx with h
  · exact Finset.mem_Icc.mp h
  · exact absurd rfl hx

lemma condE_nonneg {N : ℕ} (lab : ℤ → β) {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℤ) :
    0 ≤ condE N lab f x := by
  unfold condE
  split_ifs
  · exact div_nonneg (Finset.sum_nonneg fun y _ => hf y) (by positivity)
  · exact le_rfl

lemma condE_le {N : ℕ} (lab : ℤ → β) {f : ℤ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, f x ≤ B)
    (x : ℤ) : condE N lab f x ≤ B := by
  unfold condE
  split_ifs with hx
  · rw [div_le_iff₀ (cell_card_pos hx)]
    calc ∑ y ∈ cell N lab x, f y ≤ ∑ _y ∈ cell N lab x, B := Finset.sum_le_sum fun y _ => hf y
      _ = B * (cell N lab x).card := by simp [mul_comm]
  · exact hB

lemma condE_ge {N : ℕ} (lab : ℤ → β) {f : ℤ → ℝ} {B : ℝ} (hB : B ≤ 0) (hf : ∀ x, B ≤ f x)
    (x : ℤ) : B ≤ condE N lab f x := by
  unfold condE
  split_ifs with hx
  · rw [le_div_iff₀ (cell_card_pos hx)]
    calc B * (cell N lab x).card = ∑ _y ∈ cell N lab x, B := by simp [mul_comm]
      _ ≤ ∑ y ∈ cell N lab x, f y := Finset.sum_le_sum fun y _ => hf y
  · exact hB

/-- The conditional expectation is self-adjoint against measurable functions. -/
theorem sum_condE_mul {N : ℕ} (lab : ℤ → β) (f : ℤ → ℝ) {ψ : ℤ → ℝ} (hψ : Meas N lab ψ) :
    ∑ x ∈ Icc (1 : ℤ) N, condE N lab f x * ψ x = ∑ x ∈ Icc (1 : ℤ) N, f x * ψ x := by
  have e1 : ∀ x ∈ Icc (1 : ℤ) N, condE N lab f x * ψ x =
      ∑ y ∈ Icc (1 : ℤ) N, (if lab y = lab x then f y * ψ x / (cell N lab x).card else 0) := by
    intro x hx
    simp only [condE, if_pos hx, cell, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have e2 : ∀ x ∈ Icc (1 : ℤ) N, (if lab y = lab x then f y * ψ x / (cell N lab x).card else 0) =
      (if lab x = lab y then f y * ψ y / (cell N lab y).card else 0) := by
    intro x hx
    by_cases h : lab x = lab y
    · rw [if_pos h.symm, if_pos h, hψ x hx y hy h, cell_eq (N := N) h]
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [Finset.sum_congr rfl e2, ← Finset.sum_filter, Finset.sum_const]
  change ((cell N lab y).card : ℕ) • _ = _
  rw [nsmul_eq_mul]
  have := cell_card_pos (lab := lab) hy
  field_simp

lemma sum_condE {N : ℕ} (lab : ℤ → β) (f : ℤ → ℝ) :
    ∑ x ∈ Icc (1 : ℤ) N, condE N lab f x = ∑ x ∈ Icc (1 : ℤ) N, f x := by
  have := sum_condE_mul (N := N) lab f (ψ := fun _ => (1 : ℝ)) (fun _ _ _ _ _ => rfl)
  simpa using this

/-- **Pythagoras** for refinements. -/
theorem pythagoras {N : ℕ} {lab' : ℤ → γ} {lab : ℤ → β} (hr : Refines N lab' lab) (f : ℤ → ℝ) :
    ∑ x ∈ Icc (1 : ℤ) N, (condE N lab' f x - condE N lab f x) ^ 2 =
      energy N lab' f - energy N lab f := by
  have h1 : ∑ x ∈ Icc (1 : ℤ) N, condE N lab' f x * condE N lab f x =
      ∑ x ∈ Icc (1 : ℤ) N, condE N lab f x * condE N lab f x := by
    rw [sum_condE_mul lab' f ((condE_meas N lab f).mono hr),
      sum_condE_mul lab f (condE_meas N lab f)]
  unfold energy
  have : ∀ x, (condE N lab' f x - condE N lab f x) ^ 2 =
      condE N lab' f x ^ 2 - 2 * (condE N lab' f x * condE N lab f x) +
        condE N lab f x * condE N lab f x := fun x => by ring
  simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1]
  simp_rw [← sq]
  ring

lemma energy_nonneg (N : ℕ) (lab : ℤ → β) (f : ℤ → ℝ) : 0 ≤ energy N lab f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma energy_le {N : ℕ} (lab : ℤ → β) {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    energy N lab f ≤ N := by
  unfold energy
  calc ∑ x ∈ Icc (1 : ℤ) N, condE N lab f x ^ 2 ≤ ∑ _x ∈ Icc (1 : ℤ) N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        have h0 := condE_nonneg (N := N) lab (fun y => (hf y).1) x
        have h1 := condE_le (N := N) lab zero_le_one (fun y => (hf y).2) x
        nlinarith
    _ = N := by simp

end

end LSS

end LSSFile_CondE

section LSSFile_Grid



/-!
# Choosing a regular shift

Given reals `z x` (`x ∈ {1, …, N}`) and a scale `r`, some shift `j/m` makes few of the points
`z x + j/m` lie within `r` of an integer.
-/

open Finset

namespace LSS

noncomputable section

/-- `z` is within `r` of an integer. -/
def NearInt (r z : ℝ) : Prop := ∃ n : ℤ, |z - n| ≤ r

lemma card_int_interval_le (a L : ℝ) (hL : 0 ≤ L) (S : Finset ℤ) (hS : ∀ w ∈ S, a ≤ w ∧ (w : ℝ) ≤ a + L) :
    (S.card : ℝ) ≤ L + 1 := by
  have hsub : S ⊆ Icc ⌈a⌉ ⌊a + L⌋ := by
    intro w hw
    obtain ⟨h1, h2⟩ := hS w hw
    simp only [Finset.mem_Icc]
    exact ⟨Int.ceil_le.mpr h1, Int.le_floor.mpr h2⟩
  have hc := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  have h1 : (⌈a⌉ : ℝ) ≥ a := Int.le_ceil a
  have h2 : (⌊a + L⌋ : ℝ) ≤ a + L := Int.floor_le _
  by_cases h : ⌈a⌉ ≤ ⌊a + L⌋ + 1
  · have : ((⌊a + L⌋ + 1 - ⌈a⌉).toNat : ℤ) = ⌊a + L⌋ + 1 - ⌈a⌉ := Int.toNat_of_nonneg (by omega)
    have hc' : (S.card : ℤ) ≤ ⌊a + L⌋ + 1 - ⌈a⌉ := by omega
    have : (S.card : ℝ) ≤ (⌊a + L⌋ : ℝ) + 1 - ⌈a⌉ := by exact_mod_cast hc'
    linarith
  · have : (⌊a + L⌋ + 1 - ⌈a⌉).toNat = 0 := by omega
    rw [this] at hc
    have : S.card = 0 := by omega
    rw [this]; simp; linarith

open Classical in
lemma card_near_shifts_le (z r : ℝ) (hr : 0 ≤ r) (m : ℕ) (hm : 0 < m) :
    (((range m).filter (fun j : ℕ => NearInt r (z + j / m))).card : ℝ) ≤ 2 * r * m + 1 := by
  classical
  set S := (range m).filter (fun j : ℕ => NearInt r (z + j / m)) with hS
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let n : ℕ → ℤ := fun j => if h : NearInt r (z + j / m) then Classical.choose h else 0
  have hn : ∀ j ∈ S, |z + j / m - n j| ≤ r := by
    intro j hj
    have hP := (Finset.mem_filter.mp hj).2
    simp only [n, dif_pos hP]
    exact Classical.choose_spec hP
  let w : ℕ → ℤ := fun j => (j : ℤ) - m * n j
  have hinj : Set.InjOn w S := by
    intro i hi j hj hij
    simp only [w] at hij
    have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hdvd : (m : ℤ) ∣ (i : ℤ) - j := ⟨n i - n j, by linarith⟩
    have habs : |(i : ℤ) - j| < m := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have hcard : (S.card : ℝ) = ((S.image w).card : ℝ) := by
    rw [Finset.card_image_of_injOn hinj]
  rw [hcard]
  apply card_int_interval_le (-(m * z) - r * m) (2 * r * m) (by positivity)
  intro v hv
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  have h := hn j hj
  rw [abs_le] at h
  have e : ((w j : ℤ) : ℝ) = (j : ℝ) - m * n j := by simp [w]
  rw [e]
  have h1 : (j : ℝ) / m * m = j := by field_simp
  constructor <;> nlinarith

open Classical in
/-- **Existence of a regular shift.** -/
theorem exists_good_shift (N : ℕ) (z : ℤ → ℝ) (r : ℝ) (hr : 0 ≤ r) (m : ℕ) (hm : 0 < m) :
    ∃ j < m, ((((Icc (1 : ℤ) N).filter (fun x => NearInt r (z x + j / m))).card : ℕ) : ℝ) ≤
      N * (2 * r + 1 / m) := by
  classical
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hsum : ∑ j ∈ range m, ((((Icc (1 : ℤ) N).filter
      (fun x => NearInt r (z x + j / m))).card : ℕ) : ℝ) ≤ N * (2 * r * m + 1) := by
    have e : ∑ j ∈ range m, ((((Icc (1 : ℤ) N).filter
        (fun x => NearInt r (z x + j / m))).card : ℕ) : ℝ) =
        ∑ x ∈ Icc (1 : ℤ) N, (((range m).filter (fun j : ℕ => NearInt r (z x + j / m))).card : ℝ) := by
      simp only [Finset.card_filter]
      push_cast
      rw [Finset.sum_comm]
    rw [e]
    calc ∑ x ∈ Icc (1 : ℤ) N, (((range m).filter (fun j : ℕ => NearInt r (z x + j / m))).card : ℝ)
        ≤ ∑ _x ∈ Icc (1 : ℤ) N, (2 * r * m + 1) :=
          Finset.sum_le_sum fun x _ => card_near_shifts_le (z x) r hr m hm
      _ = N * (2 * r * m + 1) := by simp; ring
  by_contra hcon
  push_neg at hcon
  have : ∑ j ∈ range m, (N * (2 * r + 1 / m) : ℝ) < ∑ j ∈ range m, ((((Icc (1 : ℤ) N).filter
      (fun x => NearInt r (z x + j / m))).card : ℕ) : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hm⟩
      (fun j hj => hcon j (Finset.mem_range.mp hj))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have e2 : (m : ℝ) * (N * (2 * r + 1 / m)) = N * (2 * r * m + 1) := by field_simp
  linarith

end

end LSS

end LSSFile_Grid

section LSSFile_FactorIter



/-!
# Energy-increment iteration (Lemma 3.5 of Leng–Sah–Sawhney)

Iterating the inverse theorem produces structured functions `φ_0, …, φ_{T-1}` and shifts `t_i`
such that `f` is Gowers-uniform relative to the factor generated by the level sets of
`⌊K (φ_i + t_i)⌋`, and each factor is regular at scale `r`.
-/

open Finset

namespace LSS

noncomputable section

open Classical

/-- The label of `x` for the factor generated by `φ_0, …, φ_{T-1}` at resolution `K`. -/
def labF (K : ℝ) (φ : ℕ → ℤ → ℝ) (t : ℕ → ℝ) (T : ℕ) : ℤ → (Fin T → ℤ) :=
  fun x i => ⌊K * (φ i x + t i)⌋

section Iter

variable (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) (N : ℕ) (Q K r : ℝ) (m : ℕ)

/-- Invariant of the iteration. -/
def GoodData (φ : ℕ → ℤ → ℝ) (t : ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ i < T, Str N Q (φ i) ∧ (∀ x, |φ i x| ≤ Q) ∧ 0 ≤ t i ∧ t i < 1 / K ∧
    ((((Icc (1 : ℤ) N).filter (fun x => NearInt r (K * (φ i x + t i)))).card : ℕ) : ℝ) ≤
      N * (2 * r + 1 / m)

lemma labF_refines {K : ℝ} {φ φ' : ℕ → ℤ → ℝ} {t t' : ℕ → ℝ} {T : ℕ}
    (hφ : ∀ i < T, φ' i = φ i) (ht : ∀ i < T, t' i = t i) :
    Refines N (labF K φ' t' (T + 1)) (labF K φ t T) := by
  intro x _ y _ h
  funext i
  have := congrFun h ⟨i, by omega⟩
  simp only [labF] at this ⊢
  rwa [hφ i i.isLt, ht i i.isLt] at this

lemma floor_div_close {K : ℝ} (hK : 0 < K) {a t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1 / K) :
    |a - (⌊K * (a + t)⌋ : ℝ) / K| < 1 / K := by
  have h1 := Int.floor_le (K * (a + t))
  have h2 := Int.lt_floor_add_one (K * (a + t))
  have hKt : K * t < 1 := by rwa [lt_div_iff₀ hK, mul_comm] at ht1
  have e : a - (⌊K * (a + t)⌋ : ℝ) / K = (K * a - ⌊K * (a + t)⌋) / K := by field_simp
  rw [e, abs_div, abs_of_pos hK, div_lt_div_iff_of_pos_right hK, abs_lt]
  constructor <;> nlinarith

lemma sq_sum_abs_le (s : Finset ℤ) (a : ℤ → ℝ) :
    (∑ x ∈ s, |a x|) ^ 2 ≤ s.card * ∑ x ∈ s, a x ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := fun x => |a x|)
  simpa [sq_abs] using this

variable {Str N Q K r m}

/-- One step of the energy increment. -/
lemma iter_step {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 2 * Q ≤ K) (hr : 0 ≤ r) (hm : 0 < m)
    {φ : ℕ → ℤ → ℝ} {t : ℕ → ℝ} {T : ℕ} (hgood : GoodData Str N Q K r m φ t T)
    (hcorr : ∃ ψ0 : ℤ → ℝ, Str N Q ψ0 ∧ (∀ x, |ψ0 x| ≤ Q) ∧
      (N : ℝ) / Q ≤ |∑ x ∈ Icc (1 : ℤ) N, (f x - condE N (labF K φ t T) f x) * ψ0 x|) :
    ∃ φ' t', (∀ i < T, φ' i = φ i) ∧ (∀ i < T, t' i = t i) ∧ GoodData Str N Q K r m φ' t' (T + 1) ∧
      energy N (labF K φ t T) f + N / (4 * Q ^ 2 * (Q + 1) ^ 2) ≤
        energy N (labF K φ' t' (T + 1)) f := by
  have hQ0 : 0 < Q := by linarith
  have hK0 : 0 < K := by linarith
  set lab := labF K φ t T with hlab
  set g : ℤ → ℝ := fun x => f x - condE N lab f x with hg
  have hg1 : ∀ x, |g x| ≤ 1 := by
    intro x
    have h0 := condE_nonneg (N := N) lab (fun y => (hf y).1) x
    have h1 := condE_le (N := N) lab zero_le_one (fun y => (hf y).2) x
    rw [abs_le]; constructor <;> linarith [(hf x).1, (hf x).2]
  obtain ⟨ψ0, hstr, hbd, hcor⟩ := hcorr
  -- choose the shift
  obtain ⟨j, hjm, hcnt⟩ := exists_good_shift N (fun x => K * ψ0 x) r hr m hm
  set t0 : ℝ := j / (K * m) with ht0
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have ht00 : 0 ≤ t0 := by positivity
  have ht01 : t0 < 1 / K := by
    rw [ht0, div_lt_div_iff₀ (by positivity) hK0]
    have : (j : ℝ) < m := by exact_mod_cast hjm
    nlinarith
  set φ' : ℕ → ℤ → ℝ := fun i => if i < T then φ i else ψ0 with hφ'
  set t' : ℕ → ℝ := fun i => if i < T then t i else t0 with ht'
  have hφ'T : ∀ i < T, φ' i = φ i := fun i hi => by simp [hφ', hi]
  have ht'T : ∀ i < T, t' i = t i := fun i hi => by simp [ht', hi]
  have hφ'last : φ' T = ψ0 := by simp [hφ']
  have ht'last : t' T = t0 := by simp [ht']
  refine ⟨φ', t', hφ'T, ht'T, ?_, ?_⟩
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [hφ'T i hi, ht'T i hi]; exact hgood i hi
    · subst hi
      rw [hφ'last, ht'last]
      refine ⟨hstr, hbd, ht00, ht01, ?_⟩
      have e : ∀ x, K * (ψ0 x + t0) = K * ψ0 x + j / m := fun x => by
        rw [ht0]; field_simp
      have hset : (Icc (1 : ℤ) N).filter (fun x => NearInt r (K * (ψ0 x + t0))) =
          (Icc (1 : ℤ) N).filter (fun x => NearInt r (K * ψ0 x + j / m)) :=
        Finset.filter_congr (fun x _ => by rw [e x])
      rw [hset]; exact hcnt
  · set lab' := labF K φ' t' (T + 1) with hlab'
    have hrefine : Refines N lab' lab := labF_refines N hφ'T ht'T
    set ψ : ℤ → ℝ := fun x => (⌊K * (ψ0 x + t0)⌋ : ℝ) / K with hψ
    have hψmeas : Meas N lab' ψ := by
      intro x _ y _ h
      have := congrFun h ⟨T, by omega⟩
      simp only [hlab', labF, hφ'last, ht'last] at this
      simp only [hψ, this]
    have hψclose : ∀ x, |ψ0 x - ψ x| < 1 / K := fun x => floor_div_close hK0 ht00 ht01
    have hψbd : ∀ x, |ψ x| ≤ Q + 1 := by
      intro x
      have h1 := hψclose x
      have h2 := hbd x
      have : 1 / K ≤ 1 := by rw [div_le_one hK0]; linarith
      calc |ψ x| = |ψ0 x - (ψ0 x - ψ x)| := by ring_nf
        _ ≤ |ψ0 x| + |ψ0 x - ψ x| := abs_sub _ _
        _ ≤ Q + 1 := by linarith
    -- correlation with `ψ`
    have hcorψ : (N : ℝ) / (2 * Q) ≤ |∑ x ∈ Icc (1 : ℤ) N, g x * ψ x| := by
      have herr : |∑ x ∈ Icc (1 : ℤ) N, g x * ψ0 x - ∑ x ∈ Icc (1 : ℤ) N, g x * ψ x| ≤ N / K := by
        rw [← Finset.sum_sub_distrib]
        calc |∑ x ∈ Icc (1 : ℤ) N, (g x * ψ0 x - g x * ψ x)|
            ≤ ∑ x ∈ Icc (1 : ℤ) N, |g x * ψ0 x - g x * ψ x| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _x ∈ Icc (1 : ℤ) N, 1 / K := by
              refine Finset.sum_le_sum fun x _ => ?_
              rw [← mul_sub, abs_mul]
              calc |g x| * |ψ0 x - ψ x| ≤ 1 * (1 / K) :=
                    mul_le_mul (hg1 x) (hψclose x).le (abs_nonneg _) zero_le_one
                _ = 1 / K := one_mul _
          _ = N / K := by simp; ring
      have hNK : (N : ℝ) / K ≤ N / (2 * Q) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hK
      have : (N : ℝ) / Q = N / (2 * Q) + N / (2 * Q) := by field_simp; ring
      have := abs_sub_abs_le_abs_sub (∑ x ∈ Icc (1 : ℤ) N, g x * ψ0 x)
        (∑ x ∈ Icc (1 : ℤ) N, g x * ψ x)
      linarith
    -- rewrite via the refined factor
    have hsw : ∑ x ∈ Icc (1 : ℤ) N, g x * ψ x =
        ∑ x ∈ Icc (1 : ℤ) N, (condE N lab' f x - condE N lab f x) * ψ x := by
      have e1 := sum_condE_mul lab' f hψmeas
      simp only [hg, sub_mul, Finset.sum_sub_distrib]
      rw [e1]
    have hL1 : (N : ℝ) / (2 * Q) ≤
        (Q + 1) * ∑ x ∈ Icc (1 : ℤ) N, |condE N lab' f x - condE N lab f x| := by
      refine hcorψ.trans ?_
      rw [hsw]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hψbd x) (abs_nonneg _)
    have hcs := sq_sum_abs_le (Icc (1 : ℤ) N) (fun x => condE N lab' f x - condE N lab f x)
    have hcard : ((Icc (1 : ℤ) N).card : ℝ) = N := by simp
    rw [hcard, pythagoras hrefine f] at hcs
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    set S := ∑ x ∈ Icc (1 : ℤ) N, |condE N lab' f x - condE N lab f x| with hS
    have hS0 : (N : ℝ) / (2 * Q * (Q + 1)) ≤ S := by
      rw [div_le_iff₀ (by positivity)]
      have := hL1
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    have hsq : ((N : ℝ) / (2 * Q * (Q + 1))) ^ 2 ≤ N * (energy N lab' f - energy N lab f) :=
      (pow_le_pow_left₀ (by positivity) hS0 2).trans hcs
    have : (N : ℝ) / (4 * Q ^ 2 * (Q + 1) ^ 2) ≤ energy N lab' f - energy N lab f := by
      have e : ((N : ℝ) / (2 * Q * (Q + 1))) ^ 2 = N * (N / (4 * Q ^ 2 * (Q + 1) ^ 2)) := by
        field_simp; ring
      rw [e] at hsq
      exact le_of_mul_le_mul_left hsq hNr
    linarith

/-- **Factor iteration.** -/
theorem factor_iter {f : ℤ → ℝ} (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hfs : SupportedOn N f)
    (hN : 0 < N) (hQ : 1 ≤ Q) (hK : 2 * Q ≤ K) (hr : 0 ≤ r) (hm : 0 < m) {d : ℕ} {θ : ℝ}
    (hinv : ∀ g : ℤ → ℝ, (∀ x, |g x| ≤ 1) → SupportedOn N g → θ ≤ gowersZ N d g →
      ∃ φ : ℤ → ℝ, Str N Q φ ∧ (∀ x, |φ x| ≤ Q) ∧ (N : ℝ) / Q ≤ |∑ x ∈ Icc (1 : ℤ) N, g x * φ x|) :
    ∃ T : ℕ, (T : ℝ) ≤ 4 * Q ^ 2 * (Q + 1) ^ 2 + 1 ∧ ∃ φ t, GoodData Str N Q K r m φ t T ∧
      gowersZ N d (fun x => f x - condE N (labF K φ t T) f x) < θ := by
  have hQ0 : 0 < Q := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set inc : ℝ := N / (4 * Q ^ 2 * (Q + 1) ^ 2) with hinc
  have hinc0 : 0 < inc := by positivity
  have key : ∀ n : ℕ, (∃ T ≤ n, ∃ φ t, GoodData Str N Q K r m φ t T ∧
      gowersZ N d (fun x => f x - condE N (labF K φ t T) f x) < θ) ∨
      (∃ φ t, GoodData Str N Q K r m φ t n ∧ n * inc ≤ energy N (labF K φ t n) f) := by
    intro n
    induction n with
    | zero =>
      right
      refine ⟨fun _ _ => 0, fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      exact energy_nonneg _ _ _
    | succ n ih =>
      rcases ih with ⟨T, hT, rest⟩ | ⟨φ, t, hgood, hen⟩
      · exact Or.inl ⟨T, by omega, rest⟩
      by_cases hdone : gowersZ N d (fun x => f x - condE N (labF K φ t n) f x) < θ
      · exact Or.inl ⟨n, by omega, φ, t, hgood, hdone⟩
      push_neg at hdone
      set lab := labF K φ t n
      have hg1 : ∀ x, |f x - condE N lab f x| ≤ 1 := by
        intro x
        have h0 := condE_nonneg (N := N) lab (fun y => (hf y).1) x
        have h1 := condE_le (N := N) lab zero_le_one (fun y => (hf y).2) x
        rw [abs_le]; constructor <;> linarith [(hf x).1, (hf x).2]
      have hgs : SupportedOn N (fun x => f x - condE N lab f x) := by
        intro x hx
        by_contra hc
        apply hx
        have e1 : f x = 0 := by by_contra h; exact hc (hfs x h)
        have e2 : condE N lab f x = 0 := by
          by_contra h; exact hc (supportedOn_condE N lab f x h)
        simp [e1, e2]
      obtain ⟨φ', t', -, -, hgood', hen'⟩ :=
        iter_step hf hN hQ hK hr hm hgood (hinv _ hg1 hgs hdone)
      right
      refine ⟨φ', t', hgood', ?_⟩
      push_cast
      linarith
  -- conclude: the second alternative is impossible for `n` large
  set n0 : ℕ := ⌊4 * Q ^ 2 * (Q + 1) ^ 2⌋₊ + 1 with hn0
  rcases key n0 with ⟨T, hT, φ, t, hgood, hlt⟩ | ⟨φ, t, hgood, hen⟩
  · refine ⟨T, ?_, φ, t, hgood, hlt⟩
    have : (T : ℝ) ≤ n0 := by exact_mod_cast hT
    have h3 : (n0 : ℝ) ≤ 4 * Q ^ 2 * (Q + 1) ^ 2 + 1 := by
      rw [hn0]; push_cast
      linarith [Nat.floor_le (by positivity : (0:ℝ) ≤ 4 * Q ^ 2 * (Q + 1) ^ 2)]
    linarith
  · exfalso
    have h1 := energy_le (N := N) (labF K φ t n0) hf
    have h2 : (n0 : ℝ) > 4 * Q ^ 2 * (Q + 1) ^ 2 := by
      rw [hn0]; push_cast; exact Nat.lt_floor_add_one _
    have : (N : ℝ) < n0 * inc := by
      rw [hinc, mul_div_assoc', lt_div_iff₀ (by positivity)]
      nlinarith
    linarith

end Iter

end

end LSS

end LSSFile_FactorIter

section LSSFile_QP



/-!
# Quasi-polynomial bounds

`qp C x = exp (C (1 + log x)^C)` and the class `IsQP` of functions bounded by some `qp C`
on `[1, ∞)`, with its closure properties.
-/

open Real

namespace LSS

noncomputable section

lemma qp_pos (C x : ℝ) : 0 < qp C x := Real.exp_pos _

lemma one_add_log_ge_one {x : ℝ} (hx : 1 ≤ x) : 1 ≤ 1 + Real.log x := by
  have := Real.log_nonneg hx; linarith

lemma one_le_qp {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) : 1 ≤ qp C x := by
  unfold qp
  apply Real.one_le_exp
  have := one_add_log_ge_one hx
  positivity

lemma exp_le_qp {C x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) : Real.exp C ≤ qp C x := by
  unfold qp
  apply Real.exp_le_exp.mpr
  have h1 := one_add_log_ge_one hx
  have : 1 ≤ (1 + Real.log x) ^ C := Real.one_le_rpow h1 hC
  nlinarith

lemma qp_mono {C x y : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hxy : x ≤ y) : qp C x ≤ qp C y := by
  unfold qp
  apply Real.exp_le_exp.mpr
  have h1 := one_add_log_ge_one hx
  have h2 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have : (1 + Real.log x) ^ C ≤ (1 + Real.log y) ^ C :=
    Real.rpow_le_rpow (by linarith) (by linarith) hC
  exact mul_le_mul_of_nonneg_left this hC

lemma qp_mono_C {C D x : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (hx : 1 ≤ x) : qp C x ≤ qp D x := by
  unfold qp
  apply Real.exp_le_exp.mpr
  have h1 := one_add_log_ge_one hx
  have h2 : (1 + Real.log x) ^ C ≤ (1 + Real.log x) ^ D := Real.rpow_le_rpow_of_exponent_le h1 hCD
  have h3 : 0 ≤ (1 + Real.log x) ^ C := by positivity
  nlinarith

lemma le_qp_one {x : ℝ} (hx : 1 ≤ x) : x ≤ qp 1 x := by
  unfold qp
  rw [Real.rpow_one, one_mul, Real.exp_add, Real.exp_log (by linarith)]
  have : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  nlinarith

lemma qp_sq_le {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x) : qp C x * qp C x ≤ qp (2 * C) x := by
  unfold qp
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := one_add_log_ge_one hx
  have h2 : (1 + Real.log x) ^ C ≤ (1 + Real.log x) ^ (2 * C) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  nlinarith

lemma two_le_qp {C x : ℝ} (hC : 1 ≤ C) (hx : 1 ≤ x) : 2 ≤ qp C x := by
  have h := exp_le_qp (by linarith : (0 : ℝ) ≤ C) hx
  have : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have : Real.exp 1 ≤ Real.exp C := Real.exp_le_exp.mpr hC
  linarith

lemma qp_comp_le {C D x : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hx : 1 ≤ x) :
    qp C (qp D x) ≤ qp (C * (1 + D) ^ C * D) x := by
  have h1 := one_add_log_ge_one hx
  set l := Real.log x with hl
  have hlog : Real.log (qp D x) = D * (1 + l) ^ D := by simp [qp, hl]
  have hA : 1 ≤ (1 + l) ^ D := Real.one_le_rpow h1 (by linarith)
  have hB : 1 + Real.log (qp D x) ≤ (1 + D) * (1 + l) ^ D := by rw [hlog]; nlinarith
  have hpow : (1 + Real.log (qp D x)) ^ C ≤ (1 + D) ^ C * (1 + l) ^ (D * C) := by
    calc (1 + Real.log (qp D x)) ^ C ≤ ((1 + D) * (1 + l) ^ D) ^ C :=
          Real.rpow_le_rpow (by rw [hlog]; positivity) hB (by linarith)
      _ = (1 + D) ^ C * (1 + l) ^ (D * C) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by linarith)]
  have hE1 : 1 ≤ (1 + D) ^ C := Real.one_le_rpow (by linarith) (by linarith)
  have hE2 : D * C ≤ C * (1 + D) ^ C * D := by
    calc D * C = C * 1 * D := by ring
      _ ≤ C * (1 + D) ^ C * D := by gcongr
  have h3 : (1 + l) ^ (D * C) ≤ (1 + l) ^ (C * (1 + D) ^ C * D) :=
    Real.rpow_le_rpow_of_exponent_le h1 hE2
  unfold qp
  apply Real.exp_le_exp.mpr
  rw [← hl]
  have h4 : 0 ≤ (1 + l) ^ (D * C) := by positivity
  calc C * (1 + Real.log (qp D x)) ^ C ≤ C * ((1 + D) ^ C * (1 + l) ^ (D * C)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = (C * (1 + D) ^ C) * (1 + l) ^ (D * C) := by ring
    _ ≤ (C * (1 + D) ^ C * D) * (1 + l) ^ (C * (1 + D) ^ C * D) := by
        apply mul_le_mul _ h3 h4 (by positivity)
        exact le_mul_of_one_le_right (by positivity) hD

/-- Functions bounded by a quasi-polynomial on `[1, ∞)`. -/
def IsQP (F : ℝ → ℝ) : Prop := ∃ C : ℝ, 1 ≤ C ∧ ∀ X, 1 ≤ X → F X ≤ qp C X

lemma IsQP.mono {F G : ℝ → ℝ} (hG : IsQP G) (h : ∀ X, 1 ≤ X → F X ≤ G X) : IsQP F := by
  obtain ⟨C, hC, hG⟩ := hG
  exact ⟨C, hC, fun X hX => (h X hX).trans (hG X hX)⟩

lemma isQP_const (a : ℝ) : IsQP (fun _ => a) := by
  refine ⟨max 1 (Real.log (max a 1)), le_max_left _ _, fun X hX => ?_⟩
  have h := exp_le_qp (le_trans zero_le_one (le_max_left 1 (Real.log (max a 1)))) hX
  have : max a 1 ≤ Real.exp (max 1 (Real.log (max a 1))) := by
    calc max a 1 = Real.exp (Real.log (max a 1)) :=
          (Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_max_right _ _)
  linarith [le_max_left a 1]

lemma isQP_id : IsQP (fun X => X) := ⟨1, le_rfl, fun _ hX => le_qp_one hX⟩

lemma IsQP.add {F G : ℝ → ℝ} (hF : IsQP F) (hG : IsQP G) : IsQP (fun X => F X + G X) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨2 * max C D, by linarith [le_max_left C D], fun X hX => ?_⟩
  have h1 : qp C X ≤ qp (max C D) X := qp_mono_C (by linarith) (le_max_left _ _) hX
  have h2 : qp D X ≤ qp (max C D) X := qp_mono_C (by linarith) (le_max_right _ _) hX
  have h3 := two_le_qp (le_trans hC (le_max_left C D)) hX
  have h4 := qp_sq_le (le_trans hC (le_max_left C D)) hX
  have := hF X hX
  have := hG X hX
  nlinarith

lemma IsQP.mul {F G : ℝ → ℝ} (hF : IsQP F) (hG : IsQP G)
    (hG0 : ∀ X, 1 ≤ X → 0 ≤ G X) : IsQP (fun X => F X * G X) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨2 * max C D, by linarith [le_max_left C D], fun X hX => ?_⟩
  have h1 : qp C X ≤ qp (max C D) X := qp_mono_C (by linarith) (le_max_left _ _) hX
  have h2 : qp D X ≤ qp (max C D) X := qp_mono_C (by linarith) (le_max_right _ _) hX
  have h4 := qp_sq_le (le_trans hC (le_max_left C D)) hX
  calc F X * G X ≤ qp (max C D) X * qp (max C D) X :=
        mul_le_mul ((hF X hX).trans h1) ((hG X hX).trans h2) (hG0 X hX) (qp_pos _ _).le
    _ ≤ _ := h4

lemma IsQP.comp {F G : ℝ → ℝ} (hF : IsQP F) (hG : IsQP G) (hG1 : ∀ X, 1 ≤ X → 1 ≤ G X) :
    IsQP (fun X => F (G X)) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * (1 + D) ^ C * D, ?_, fun X hX => ?_⟩
  · have : 1 ≤ (1 + D) ^ C := Real.one_le_rpow (by linarith) (by linarith)
    have : 1 ≤ C * (1 + D) ^ C := by nlinarith
    nlinarith
  calc F (G X) ≤ qp C (G X) := hF _ (hG1 X hX)
    _ ≤ qp C (qp D X) := qp_mono (by linarith) (hG1 X hX) (hG X hX)
    _ ≤ _ := qp_comp_le hC hD hX

lemma isQP_qp {C : ℝ} (hC : 1 ≤ C) : IsQP (fun X => qp C X) := ⟨C, hC, fun _ _ => le_rfl⟩

lemma IsQP.pow {F : ℝ → ℝ} (hF : IsQP F) (hF0 : ∀ X, 1 ≤ X → 0 ≤ F X) :
    ∀ n : ℕ, IsQP (fun X => F X ^ n)
  | 0 => by simpa using isQP_const 1
  | n + 1 => by
    have := (IsQP.pow hF hF0 n).mul hF hF0
    simpa [pow_succ] using this

end

end LSS

end LSSFile_QP

section LSSFile_DensIncr



/-!
# The density increment lemma (Lemma 3.4 of Leng–Sah–Sawhney)
-/

open Finset

namespace LSS

noncomputable section

open Classical

/-- The complexity bound `Q = qp C_I (1/η)`. -/
def pQ (k : ℕ) (CI δ : ℝ) : ℝ := qp CI (1 / etaK k δ)

/-- The bound on the number of energy-increment steps. -/
def pT (k : ℕ) (CI δ : ℝ) : ℝ := 4 * pQ k CI δ ^ 2 * (pQ k CI δ + 1) ^ 2 + 1

/-- The Schmidt parameter `V`. -/
def pV (k : ℕ) (CI CS δ : ℝ) : ℝ := qp CS ((pT k CI δ + 2) * (pQ k CI δ + 2))

/-- `ω₀ = δ^k / (5120 k²)`. -/
def pω (k : ℕ) (δ : ℝ) : ℝ := δ ^ k / (5120 * (k : ℝ) ^ 2)

/-- The largeness threshold. -/
def pB (k : ℕ) (CI CS δ : ℝ) : ℝ :=
  4 * k + 128 * k * (1 / δ) ^ k +
    12 * pT k CI δ * (2 * pQ k CI δ) * pV k CI CS δ / (cpK k * δ * pω k δ) +
    8 / (cpK k * δ * pω k δ)

lemma nearInt_of_floor_ne {a b z r : ℝ} (h : ⌊a⌋ ≠ ⌊b⌋) (ha : |z - a| ≤ r) (hb : |z - b| ≤ r) :
    NearInt r z := by
  rcases lt_or_gt_of_ne h with h' | h'
  · refine ⟨⌊b⌋, ?_⟩
    have h1 : (⌊a⌋ : ℝ) + 1 ≤ ⌊b⌋ := by exact_mod_cast h'
    have h2 := Int.lt_floor_add_one a
    have h3 := Int.floor_le b
    rw [abs_le] at ha hb ⊢
    constructor
    · rcases le_total z ⌊b⌋ with hz | hz <;> linarith
    · rcases le_total z ⌊b⌋ with hz | hz <;> linarith
  · refine ⟨⌊a⌋, ?_⟩
    have h1 : (⌊b⌋ : ℝ) + 1 ≤ ⌊a⌋ := by exact_mod_cast h'
    have h2 := Int.lt_floor_add_one b
    have h3 := Int.floor_le a
    rw [abs_le] at ha hb ⊢
    constructor
    · rcases le_total z ⌊a⌋ with hz | hz <;> linarith
    · rcases le_total z ⌊a⌋ with hz | hz <;> linarith

lemma etaK_pos {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) : 0 < etaK k δ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold etaK; positivity

lemma etaK_le_half {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : etaK k δ ≤ 1 / 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [etaK, div_le_iff₀ (by positivity)]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : δ ^ k ≤ 1 := pow_le_one₀ hδ0.le hδ1
  nlinarith

lemma one_le_inv_etaK {k : ℕ} (hk : 1 ≤ k) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ 1 / etaK k δ := by
  have := etaK_le_half hk hδ0 hδ1
  rw [le_div_iff₀ (etaK_pos hk hδ0)]; linarith

lemma pQ_ge_one {k : ℕ} (hk : 1 ≤ k) {CI δ : ℝ} (hCI : 0 < CI) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ pQ k CI δ :=
  one_le_qp hCI.le (one_le_inv_etaK hk hδ0 hδ1)

lemma small_numeric {Bc L Ns Nst N Tm r K V B cp δ ω0 : ℝ} (hcp : 0 ≤ cp) (hδ : 0 ≤ δ)
    (hω : 0 ≤ ω0) (hNs : 0 < Ns) (hN : 0 ≤ N)
    (hBc : Bc ≤ Tm * (3 * r * N)) (hPL : L * Nst ≤ 2 * N) (hrσ : r * Ns = K * V)
    (hB1 : 12 * Tm * K * V ≤ B * (cp * δ * ω0)) (hBσ : B ≤ Ns) :
    Bc + L * (cp / 8 * δ * ω0 * Nst) ≤ cp / 2 * δ * ω0 * N := by
  have h1 : L * (cp / 8 * δ * ω0 * Nst) ≤ cp / 8 * δ * ω0 * (2 * N) := by
    have : L * (cp / 8 * δ * ω0 * Nst) = cp / 8 * δ * ω0 * (L * Nst) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hPL (by positivity)
  have h2 : 12 * Tm * r * Ns ≤ cp * δ * ω0 * Ns := by
    calc 12 * Tm * r * Ns = 12 * Tm * K * V := by rw [mul_assoc, hrσ]; ring
      _ ≤ B * (cp * δ * ω0) := hB1
      _ ≤ Ns * (cp * δ * ω0) := mul_le_mul_of_nonneg_right hBσ (by positivity)
      _ = cp * δ * ω0 * Ns := by ring
  have h12 : 12 * Tm * r ≤ cp * δ * ω0 := le_of_mul_le_mul_right h2 hNs
  have h3 : Tm * (3 * r * N) ≤ cp * δ * ω0 * N / 4 := by
    calc Tm * (3 * r * N) = (12 * Tm * r) * N / 4 := by ring
      _ ≤ (cp * δ * ω0) * N / 4 := by gcongr
  linarith

lemma length_numeric {Y B Ns Nst c : ℝ} (hY : 0 ≤ Y) (hc : 0 ≤ c) (hB2 : 8 ≤ B * c)
    (hYB : B * Y ≤ Ns) (hσ : Ns ≤ Nst) : Y ≤ c / 8 * Nst := by
  have : Y ≤ c / 8 * (B * Y) := by nlinarith
  calc Y ≤ c / 8 * (B * Y) := this
    _ ≤ c / 8 * Nst := mul_le_mul_of_nonneg_left (hYB.trans hσ) (by positivity)

set_option maxHeartbeats 1600000 in
/-- **Density increment lemma**, explicit form. -/
theorem dens_incr_explicit (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) {k : ℕ} (hk : 3 ≤ k) {CI CS : ℝ}
    (hCI : 0 < CI) (hCS : 0 < CS) (hI : InvWith Str (k - 2) CI) (hS : SchmidtWith Str CS)
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hAne : A.Nonempty) (hfree : ¬ Erdos142.HasAP k A)
    (hlarge : pB k CI CS (A.card / N) ≤ (N : ℝ) ^ (1 / (2 * pV k CI CS (A.card / N)))) :
    ∃ (a : ℤ) (d M : ℕ), 0 < d ∧ (N : ℝ) ^ (1 / (2 * pV k CI CS (A.card / N))) ≤ M ∧
      apSet a d M ⊆ Icc (1 : ℤ) N ∧
      (1 + cpK k / 2) * (A.card / N) * M ≤ ∑ x ∈ apSet a d M, ind A x := by
  -- basic quantities
  set δ : ℝ := A.card / N with hδ
  have hNpos : 0 < N := by
    obtain ⟨x, hx⟩ := hAne
    have := Finset.mem_Icc.mp (hA hx); omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hAne.card_pos
  have hAN : (A.card : ℝ) ≤ N := by
    have := Finset.card_le_card hA; simp at this; exact_mod_cast this
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδ, div_le_one hNr]; exact hAN
  have hk1 : 1 ≤ k := by omega
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set η := etaK k δ with hη
  have hη0 : 0 < η := etaK_pos hk1 hδ0
  have hη1 : η ≤ 1 / 2 := etaK_le_half hk1 hδ0 hδ1
  set Q := pQ k CI δ with hQ
  have hQ1 : 1 ≤ Q := pQ_ge_one hk1 hCI hδ0 hδ1
  set K : ℝ := 2 * Q with hK
  set Tm := pT k CI δ with hTm
  have hT0 : 0 ≤ Tm := by rw [hTm, pT]; positivity
  set V := pV k CI CS δ with hV
  have hV1 : 1 ≤ V := one_le_qp hCS.le
    (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith))
  set σ : ℝ := 1 / V with hσ
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 1 := by rw [hσ, div_le_one (by linarith)]; exact hV1
  set cp := cpK k with hcp
  have hcp0 : 0 < cp := by rw [hcp, cpK]; positivity
  set ω0 := pω k δ with hω0
  have hω00 : 0 < ω0 := by rw [hω0, pω]; positivity
  -- consequences of largeness
  set B := pB k CI CS δ with hB
  set Y : ℝ := (N : ℝ) ^ (1 / (2 * V)) with hY
  have hY1 : 1 ≤ Y := Real.one_le_rpow hN1 (by positivity)
  have hYN : Y ≤ N := by
    calc Y ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by
            rw [div_le_one (by linarith)]; linarith)
      _ = N := Real.rpow_one _
  have hYσ : (N : ℝ) ^ σ = Y * Y := by
    rw [hY, ← Real.rpow_add hNr]; congr 1; rw [hσ]; field_simp; ring
  have hB1 : 12 * Tm * K * V / (cp * δ * ω0) ≤ B := by
    rw [hB, pB]
    have : 0 ≤ 4 * (k : ℝ) + 128 * k * (1 / δ) ^ k := by positivity
    have : 0 ≤ 8 / (cp * δ * ω0) := by positivity
    linarith
  have hB2 : 8 / (cp * δ * ω0) ≤ B := by
    rw [hB, pB]
    have : 0 ≤ 4 * (k : ℝ) + 128 * k * (1 / δ) ^ k := by positivity
    have : 0 ≤ 12 * Tm * K * V / (cp * δ * ω0) := by positivity
    linarith
  have hB3 : 4 * (k : ℝ) + 128 * k * (1 / δ) ^ k ≤ B := by
    rw [hB, pB]
    have : 0 ≤ 12 * Tm * K * V / (cp * δ * ω0) := by positivity
    have : 0 ≤ 8 / (cp * δ * ω0) := by positivity
    linarith
  have hBN : B ≤ N := hlarge.trans hYN
  have hN4 : 4 * k ≤ N := by
    have : (4 * k : ℝ) ≤ N := by
      have : 0 ≤ 128 * (k : ℝ) * (1 / δ) ^ k := by positivity
      linarith
    exact_mod_cast this
  have hN128 : 128 * k * ((N : ℝ) / A.card) ^ k ≤ N := by
    have e : (N : ℝ) / A.card = 1 / δ := by rw [hδ]; field_simp
    rw [e]; linarith
  -- the regularity scale `r` and grid size `m`
  set r : ℝ := K * V * (N : ℝ) ^ (-σ) with hr
  have hr0 : 0 < r := by positivity
  set m : ℕ := ⌈1 / r⌉₊ + 1 with hm
  have hm0 : 0 < m := by omega
  have hmr : 1 / (m : ℝ) ≤ r := by
    have h1 : 1 / r ≤ m := by rw [hm]; push_cast; linarith [Nat.le_ceil (1 / r)]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hr0] at h1
    linarith
  -- the inverse theorem at level `η`
  have hinv : ∀ g : ℤ → ℝ, (∀ x, |g x| ≤ 1) → SupportedOn N g →
      η ^ (2 ^ (k - 1)) * (N : ℝ) ^ k ≤ gowersZ N (k - 1) g →
      ∃ φ : ℤ → ℝ, Str N Q φ ∧ (∀ x, |φ x| ≤ Q) ∧
        (N : ℝ) / Q ≤ |∑ x ∈ Icc (1 : ℤ) N, g x * φ x| := by
    intro g hg1 hgs hgow
    have e1 : k - 2 + 1 = k - 1 := by omega
    have e2 : k - 2 + 2 = k := by omega
    exact hI N η g hη0 hη1 hg1 hgs (by rw [e1, e2]; exact hgow)
  obtain ⟨T, hT, φ, t, hgood, hgow⟩ := factor_iter (Str := Str) (N := N) (Q := Q) (K := K)
    (r := r) (m := m) (f := ind A) (fun x => ⟨ind_nonneg _ _, ind_le_one _ _⟩)
    (supportedOn_ind hA) hNpos hQ1 (le_refl _) hr0.le hm0 hinv
  have hTm' : (T : ℝ) ≤ Tm := by rw [hTm, pT]; exact hT
  set lab := labF K φ t T with hlab
  set F := condE N lab (ind A) with hF
  have hF01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1 := fun x =>
    ⟨condE_nonneg lab (fun y => ind_nonneg _ _) x, condE_le lab zero_le_one (fun y => ind_le_one _ _) x⟩
  have hFs : SupportedOn N F := supportedOn_condE N lab _
  have hFsum : ∑ x ∈ Icc (1 : ℤ) N, F x = A.card := by
    rw [hF, sum_condE, sum_ind hA]
  -- a prime `2N < p ≤ 4N`
  obtain ⟨p, hpp, hp1, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  haveI : Fact p.Prime := ⟨hpp⟩
  have hΩ := omega_large (p := p) hk hA hAne hfree hp1 (by omega) hN128 hN4 hF01 hFs hFsum hgow
  set Ω := (Icc (1 : ℤ) N).filter (fun x => (1 + cp) * δ < F x) with hΩdef
  -- Schmidt
  obtain ⟨P, hPL, hPvar⟩ := hS N T Q (fun i => φ i) hQ1 (fun i => (hgood i i.isLt).1)
  set Vt : ℝ := qp CS ((T + 2) * (Q + 2)) with hVt
  have hTr0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hR1 : (1 : ℝ) ≤ (T + 2) * (Q + 2) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hVtV : Vt ≤ V := by
    rw [hVt, hV, pV]
    exact qp_mono hCS.le hR1 (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
  have hVt1 : 1 ≤ Vt := one_le_qp hCS.le hR1
  set σt : ℝ := 1 / Vt with hσt
  have hσσt : σ ≤ σt := by
    rw [hσ, hσt]; exact one_div_le_one_div_of_le (by linarith) hVtV
  have hvar : ∀ (i : Fin T) j, ∀ x ∈ P.piece j, ∀ y ∈ P.piece j, K * |φ i x - φ i y| ≤ r := by
    intro i j x hx y hy
    have h1 := hPvar i j x hx y hy
    have h2 : (N : ℝ) ^ (-(1 / Vt)) ≤ (N : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by rw [← hσt]; linarith)
    have h3 : Vt * (N : ℝ) ^ (-(1 / Vt)) ≤ V * (N : ℝ) ^ (-σ) :=
      mul_le_mul hVtV h2 (by positivity) (by linarith)
    have hK0 : 0 ≤ K := by rw [hK]; linarith
    calc K * |φ i x - φ i y| ≤ K * (V * (N : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (h1.trans h3) hK0
      _ = r := by rw [hr]; ring
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  -- the bad set: points near a cell boundary of some factor
  set Bad : Finset ℤ := (Finset.univ : Finset (Fin T)).biUnion
    (fun i => (Icc (1 : ℤ) N).filter (fun x => NearInt r (K * (φ i x + t i)))) with hBad
  have hBadcard : (Bad.card : ℝ) ≤ Tm * (3 * r * N) := by
    have h1 : Bad.card ≤ ∑ i : Fin T,
        ((Icc (1 : ℤ) N).filter (fun x => NearInt r (K * (φ i x + t i)))).card :=
      Finset.card_biUnion_le
    have h2 : ∀ i : Fin T, ((((Icc (1 : ℤ) N).filter
        (fun x => NearInt r (K * (φ i x + t i)))).card : ℕ) : ℝ) ≤ 3 * r * N := by
      intro i
      have h := (hgood i i.isLt).2.2.2.2
      calc _ ≤ N * (2 * r + 1 / m) := h
        _ ≤ N * (2 * r + r) := by gcongr
        _ = 3 * r * N := by ring
    have h3 : (Bad.card : ℝ) ≤ ∑ i : Fin T, ((((Icc (1 : ℤ) N).filter
        (fun x => NearInt r (K * (φ i x + t i)))).card : ℕ) : ℝ) := by exact_mod_cast h1
    calc (Bad.card : ℝ) ≤ ∑ _i : Fin T, 3 * r * N := h3.trans (Finset.sum_le_sum fun i _ => h2 i)
      _ = T * (3 * r * N) := by simp
      _ ≤ Tm * (3 * r * N) := by gcongr
  -- crossing pieces lie in the bad set
  have hcross : ∀ j, (∃ x ∈ P.piece j, x ∈ Ω) → ¬ P.piece j ⊆ Ω → P.piece j ⊆ Bad := by
    rintro j ⟨x0, hx0, hx0Ω⟩ hnot z hz
    obtain ⟨y0, hy0, hy0Ω⟩ := Finset.not_subset.mp hnot
    have hx0I := P.piece_subset j hx0
    have hy0I := P.piece_subset j hy0
    have hzI := P.piece_subset j hz
    have hFx : (1 + cp) * δ < F x0 := (Finset.mem_filter.mp hx0Ω).2
    have hFy : ¬ ((1 + cp) * δ < F y0) := fun h => hy0Ω (Finset.mem_filter.mpr ⟨hy0I, h⟩)
    have hlab : lab x0 ≠ lab y0 := by
      intro h
      have e : F x0 = F y0 := condE_meas N lab (ind A) x0 hx0I y0 hy0I h
      rw [e] at hFx
      exact hFy hFx
    obtain ⟨i, hi⟩ : ∃ i : Fin T, lab x0 i ≠ lab y0 i := by
      by_contra h; push_neg at h; exact hlab (funext h)
    have hnear : NearInt r (K * (φ i z + t i)) := by
      apply nearInt_of_floor_ne (a := K * (φ i x0 + t i)) (b := K * (φ i y0 + t i)) hi
      · rw [show K * (φ i z + t i) - K * (φ i x0 + t i) = K * (φ i z - φ i x0) by ring,
          abs_mul, abs_of_nonneg hK0]
        exact hvar i j z hz x0 hx0
      · rw [show K * (φ i z + t i) - K * (φ i y0 + t i) = K * (φ i z - φ i y0) by ring,
          abs_mul, abs_of_nonneg hK0]
        exact hvar i j z hz y0 hy0
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hzI, hnear⟩⟩
  -- the density of `A` on `Ω`
  have hΩsub : Ω ⊆ Icc (1 : ℤ) N := Finset.filter_subset _ _
  have hsumΩ : (1 + cp) * δ * Ω.card ≤ ∑ x ∈ Ω, ind A x := by
    have hmeas : Meas N lab (fun x => if x ∈ Ω then (1 : ℝ) else 0) := by
      intro x hx y hy h
      have e : F x = F y := condE_meas N lab (ind A) x hx y hy h
      simp only [hΩdef, Finset.mem_filter, hx, hy, true_and, e]
    have e := sum_condE_mul lab (ind A) hmeas
    simp_rw [mul_ite, mul_one, mul_zero] at e
    rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hΩsub] at e
    rw [← e]
    calc (1 + cp) * δ * Ω.card = ∑ _x ∈ Ω, (1 + cp) * δ := by simp; ring
      _ ≤ ∑ x ∈ Ω, F x := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
  -- parameters for the pigeonhole
  have hΩcard : ω0 * N ≤ Ω.card := hΩ
  have hΩne : Ω.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Ω.card := lt_of_lt_of_le (by positivity) hΩcard
    exact_mod_cast this
  set β : ℝ := cp / 2 * δ * ω0 * N with hβ
  set N' : ℝ := cp / 8 * δ * ω0 * (N : ℝ) ^ σt with hN'
  have hNσt : (N : ℝ) ^ σ ≤ (N : ℝ) ^ σt := Real.rpow_le_rpow_of_exponent_le hN1 hσσt
  have hB0 : 1 ≤ B := by
    have : (4 : ℝ) ≤ 4 * k := by linarith
    have : 0 ≤ 128 * (k : ℝ) * (1 / δ) ^ k := by positivity
    linarith
  have hYB : B * Y ≤ (N : ℝ) ^ σ := by
    rw [hYσ]; exact mul_le_mul_of_nonneg_right hlarge (by linarith)
  have hBσ : B ≤ (N : ℝ) ^ σ := le_trans (le_mul_of_one_le_right (by linarith) hY1) hYB
  have hTm1 : 1 ≤ Tm := by
    rw [hTm, pT]; have : 0 ≤ 4 * Q ^ 2 * (Q + 1) ^ 2 := by positivity
    linarith
  have hrσ : r * (N : ℝ) ^ σ = K * V := by
    rw [hr, mul_assoc, ← Real.rpow_add hNr]; simp
  have hB1' : 12 * Tm * K * V ≤ B * (cp * δ * ω0) := by
    have h := hB1
    rw [div_le_iff₀ (by positivity)] at h
    exact h
  have hsmall : (Bad.card : ℝ) + P.L * N' ≤ β :=
    small_numeric hcp0.le hδ0.le hω00.le (by positivity) hNr.le
      hBadcard hPL hrσ hB1' hBσ
  have hβΩ : β ≤ ((1 + cp) * δ - (1 + cp / 2) * δ) * Ω.card := by
    have e : ((1 + cp) * δ - (1 + cp / 2) * δ) = cp / 2 * δ := by ring
    rw [e, hβ, mul_assoc (cp / 2 * δ)]
    gcongr
  obtain ⟨j, hjlen, hjsub, hjsum⟩ := piece_increment P (ind A) (ind_nonneg A) (ind_le_one A) Ω Bad
    hΩsub N' ((1 + cp) * δ) ((1 + cp / 2) * δ) β
    (mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hcp0.le (by norm_num)) hδ0.le) hω00.le)
      (Real.rpow_nonneg hNr.le _)) (mul_pos (by linarith) hδ0) hΩne hsumΩ
    hcross hsmall hβΩ
  refine ⟨P.a j, P.d j, P.len j, P.hd j, ?_, P.piece_subset j, hjsum⟩
  -- the length
  refine le_trans ?_ hjlen
  rw [hN']
  have hB2' : 8 ≤ B * (cp * δ * ω0) := by
    have h := hB2
    rw [div_le_iff₀ (by positivity)] at h
    exact h
  have hlen := length_numeric (c := cp * δ * ω0) (by linarith)
    (mul_nonneg (mul_nonneg hcp0.le hδ0.le) hω00.le) hB2' hYB hNσt
  calc Y ≤ cp * δ * ω0 / 8 * (N : ℝ) ^ σt := hlen
    _ = cp / 8 * δ * ω0 * (N : ℝ) ^ σt := by ring

end

end LSS

end LSSFile_DensIncr

section LSSFile_QPBounds



/-!
# Quasi-polynomial control of the parameters of the density increment lemma
-/

namespace LSS

noncomputable section

lemma isQP_monomial (c : ℝ) (k : ℕ) : IsQP (fun X => c * X ^ k) :=
  (isQP_const c).mul (isQP_id.pow (fun X hX => by linarith) k) (fun X hX => by positivity)

lemma isQP_qp' {C : ℝ} (hC : 0 < C) : IsQP (fun X => qp C X) :=
  (isQP_qp (le_max_right C 1)).mono (fun X hX => qp_mono_C hC.le (le_max_left _ _) hX)

lemma inv_etaK_inv {k : ℕ} {X : ℝ} (hX : 0 < X) :
    1 / etaK k (1 / X) = 1024 * (k : ℝ) ^ 2 * X ^ k := by
  unfold etaK
  rw [one_div_div, one_div_pow, div_div_eq_mul_div, div_one]

lemma one_le_monomial {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) : 1 ≤ 1024 * (k : ℝ) ^ 2 * X ^ k := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have : 1 ≤ X ^ k := one_le_pow₀ hX
  have : 1 ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk'
  nlinarith

lemma isQP_pQ {k : ℕ} (hk : 1 ≤ k) {CI : ℝ} (hCI : 0 < CI) : IsQP (fun X => pQ k CI (1 / X)) := by
  refine ((isQP_qp' hCI).comp (isQP_monomial (1024 * (k : ℝ) ^ 2) k)
    (fun X hX => one_le_monomial hk hX)).mono (fun X hX => ?_)
  simp only [pQ, inv_etaK_inv (by linarith : (0 : ℝ) < X)]
  exact le_rfl

lemma pQ_ge_one' {k : ℕ} (hk : 1 ≤ k) {CI : ℝ} (hCI : 0 < CI) {X : ℝ} (hX : 1 ≤ X) :
    1 ≤ pQ k CI (1 / X) :=
  pQ_ge_one hk hCI (by positivity) (by rw [div_le_one (by linarith)]; exact hX)

lemma isQP_pT {k : ℕ} (hk : 1 ≤ k) {CI : ℝ} (hCI : 0 < CI) : IsQP (fun X => pT k CI (1 / X)) := by
  have hQ := isQP_pQ hk hCI
  have hQ0 : ∀ X, 1 ≤ X → 0 ≤ pQ k CI (1 / X) := fun X hX => by
    linarith [pQ_ge_one' hk hCI hX]
  have h1 := ((isQP_const 4).mul (hQ.pow hQ0 2) (fun X hX => by positivity)).mul
    ((hQ.add (isQP_const 1)).pow (fun X hX => by linarith [hQ0 X hX]) 2)
    (fun X hX => by positivity)
  exact (h1.add (isQP_const 1)).mono (fun X hX => le_of_eq (by simp [pT]))

lemma pT_ge_one {k : ℕ} (hk : 1 ≤ k) {CI : ℝ} (hCI : 0 < CI) {X : ℝ} (hX : 1 ≤ X) :
    1 ≤ pT k CI (1 / X) := by
  unfold pT
  have : 0 ≤ 4 * pQ k CI (1 / X) ^ 2 * (pQ k CI (1 / X) + 1) ^ 2 := by
    have := pQ_ge_one' hk hCI hX; positivity
  linarith

lemma isQP_pV {k : ℕ} (hk : 1 ≤ k) {CI CS : ℝ} (hCI : 0 < CI) (hCS : 0 < CS) :
    IsQP (fun X => pV k CI CS (1 / X)) := by
  have hG : IsQP (fun X => (pT k CI (1 / X) + 2) * (pQ k CI (1 / X) + 2)) :=
    ((isQP_pT hk hCI).add (isQP_const 2)).mul ((isQP_pQ hk hCI).add (isQP_const 2))
      (fun X hX => by linarith [pQ_ge_one' hk hCI hX])
  refine ((isQP_qp' hCS).comp hG (fun X hX => ?_)).mono (fun X hX => le_rfl)
  have := pQ_ge_one' hk hCI hX
  have := pT_ge_one hk hCI hX
  nlinarith

lemma pV_ge_one {k : ℕ} (hk : 1 ≤ k) {CI CS : ℝ} (hCI : 0 < CI) (hCS : 0 < CS) {X : ℝ}
    (hX : 1 ≤ X) : 1 ≤ pV k CI CS (1 / X) := by
  unfold pV
  apply one_le_qp hCS.le
  have := pQ_ge_one' hk hCI hX
  have := pT_ge_one hk hCI hX
  nlinarith

lemma inv_cpK_mul {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 0 < X) :
    1 / (cpK k * (1 / X) * pω k (1 / X)) = 8192 * 5120 * (k : ℝ) ^ 4 * X ^ (k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold cpK pω
  field_simp
  rw [one_div_pow, pow_succ]
  field_simp

lemma isQP_pB {k : ℕ} (hk : 1 ≤ k) {CI CS : ℝ} (hCI : 0 < CI) (hCS : 0 < CS) :
    IsQP (fun X => pB k CI CS (1 / X)) := by
  have hQ := isQP_pQ hk hCI
  have hT := isQP_pT hk hCI
  have hV := isQP_pV hk hCI hCS
  have hM := isQP_monomial (8192 * 5120 * (k : ℝ) ^ 4) (k + 1)
  have hM0 : ∀ X, 1 ≤ X → 0 ≤ 8192 * 5120 * (k : ℝ) ^ 4 * X ^ (k + 1) := fun X hX => by
    positivity
  have h1 := (((isQP_const 12).mul hT (fun X hX => by linarith [pT_ge_one hk hCI hX])).mul
    ((isQP_const 2).mul hQ (fun X hX => by linarith [pQ_ge_one' hk hCI hX]))
    (fun X hX => by linarith [pQ_ge_one' hk hCI hX])).mul hV
    (fun X hX => by linarith [pV_ge_one hk hCI hCS hX])
  have h2 := h1.mul hM hM0
  have h3 := (isQP_const 8).mul hM hM0
  have h4 := (((isQP_const (4 * k)).add (isQP_monomial (128 * k) k)).add h2).add h3
  refine h4.mono (fun X hX => le_of_eq ?_)
  have hX0 : (0 : ℝ) < X := by linarith
  have e := inv_cpK_mul hk hX0
  simp only [pB, one_div_one_div]
  rw [div_eq_mul_one_div (12 * _ * _ * _), div_eq_mul_one_div 8, e]

lemma pB_pos {k : ℕ} (hk : 1 ≤ k) {CI CS : ℝ} (hCI : 0 < CI) (hCS : 0 < CS) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 0 < pB k CI CS δ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hQ := pQ_ge_one hk hCI hδ0 hδ1
  have hT : 0 ≤ pT k CI δ := by unfold pT; positivity
  have hV : 0 ≤ pV k CI CS δ := (qp_pos _ _).le
  unfold pB cpK pω
  positivity

/-- Quasi-polynomial control of the parameters of the density increment lemma. -/
theorem param_bounds {k : ℕ} (hk : 1 ≤ k) {CI CS : ℝ} (hCI : 0 < CI) (hCS : 0 < CS) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      2 * pV k CI CS δ ≤ qp C (1 / δ) ∧
      2 * pV k CI CS δ * Real.log (pB k CI CS δ) ≤ qp C (1 / δ) := by
  have hV := isQP_pV hk hCI hCS
  have h1 := (isQP_const 2).mul hV (fun X hX => by linarith [pV_ge_one hk hCI hCS hX])
  have h2 := h1.mul (isQP_pB hk hCI hCS) (fun X hX => by
    have := pB_pos hk hCI hCS (δ := 1 / X) (by positivity)
      (by rw [div_le_one (by linarith)]; exact hX)
    exact this.le)
  obtain ⟨C1, hC1, h1⟩ := h1
  obtain ⟨C2, hC2, h2⟩ := h2
  refine ⟨max C1 C2, le_trans hC1 (le_max_left _ _), fun δ hδ0 hδ1 => ?_⟩
  have hX : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have e : 1 / (1 / δ) = δ := one_div_one_div δ
  have a1 := h1 (1 / δ) hX
  have a2 := h2 (1 / δ) hX
  simp only [e] at a1 a2
  have m1 := qp_mono_C (by linarith) (le_max_left C1 C2) hX
  have m2 := qp_mono_C (by linarith) (le_max_right C1 C2) hX
  have hB := pB_pos hk hCI hCS hδ0 hδ1
  have hlog : Real.log (pB k CI CS δ) ≤ pB k CI CS δ := by
    have := Real.add_one_le_exp (Real.log (pB k CI CS δ))
    rw [Real.exp_log hB] at this; linarith
  have hV0 : 0 ≤ 2 * pV k CI CS δ := by have := qp_pos CS ((pT k CI δ + 2) * (pQ k CI δ + 2)); unfold pV; linarith
  refine ⟨a1.trans m1, ?_⟩
  calc 2 * pV k CI CS δ * Real.log (pB k CI CS δ) ≤ 2 * pV k CI CS δ * pB k CI CS δ :=
        mul_le_mul_of_nonneg_left hlog hV0
    _ ≤ _ := a2.trans m2

end

end LSS

end LSSFile_QPBounds

section LSSFile_Reduction



/-!
# Iterating the density increment
-/

open Finset

namespace LSS

noncomputable section

open Classical

/-- The set `{i + 1 : i < M, a + d i ∈ A}`: the trace of `A` on the progression `apSet a d M`,
rescaled to `{1, …, M}`. -/
def rescale (A : Finset ℕ) (a : ℤ) (d M : ℕ) : Finset ℕ :=
  ((range M).filter (fun i : ℕ => 0 ≤ a + d * i ∧ (a + d * i).toNat ∈ A)).image (· + 1)

lemma rescale_subset (A : Finset ℕ) (a : ℤ) (d M : ℕ) : rescale A a d M ⊆ Icc 1 M := by
  intro x hx
  simp only [rescale, mem_image, mem_filter, mem_range] at hx
  obtain ⟨i, ⟨hi, -⟩, rfl⟩ := hx
  simp only [mem_Icc]; omega

lemma rescale_card (A : Finset ℕ) (a : ℤ) {d : ℕ} (hd : 0 < d) (M : ℕ) :
    ((rescale A a d M).card : ℝ) = ∑ x ∈ apSet a d M, ind A x := by
  unfold rescale apSet
  rw [card_image_of_injective _ (add_left_injective 1)]
  rw [sum_image (fun i _ j _ h => by
    have : (d : ℤ) * i = d * j := by linarith
    have := mul_left_cancel₀ (by exact_mod_cast hd.ne' : (d : ℤ) ≠ 0) this
    exact_mod_cast this)]
  rw [card_filter]
  push_cast
  refine sum_congr rfl (fun i _ => ?_)
  simp only [ind]

lemma rescale_free {k : ℕ} (hk : 1 ≤ k) {A : Finset ℕ} {a : ℤ} {d M : ℕ} (hd : 0 < d)
    (hfree : ¬ Erdos142.HasAP k A) : ¬ Erdos142.HasAP k (rescale A a d M) := by
  rintro ⟨b, e, he, hb⟩
  apply hfree
  have hmem : ∀ i < k, 0 ≤ a + d * ((b + i * e - 1 : ℕ) : ℤ) ∧
      (a + d * ((b + i * e - 1 : ℕ) : ℤ)).toNat ∈ A ∧ 1 ≤ b + i * e := by
    intro i hi
    have := hb i hi
    simp only [rescale, mem_image, mem_filter, mem_range] at this
    obtain ⟨j, ⟨-, h0, h1⟩, hj⟩ := this
    have : b + i * e - 1 = j := by omega
    rw [this]; exact ⟨h0, h1, by omega⟩
  have hb1 : 1 ≤ b := by have := (hmem 0 (by omega)).2.2; simpa using this
  refine ⟨(a + d * ((b - 1 : ℕ) : ℤ)).toNat, d * e, Nat.mul_pos hd he, fun i hi => ?_⟩
  obtain ⟨h0, h1, -⟩ := hmem i hi
  obtain ⟨g0, -, -⟩ := hmem 0 (by omega)
  simp only [zero_mul, add_zero] at g0
  convert h1 using 1
  have e1 : ((b + i * e - 1 : ℕ) : ℤ) = ((b - 1 : ℕ) : ℤ) + i * e := by
    push_cast [Nat.sub_add_comm hb1, hb1]
    omega
  rw [e1]
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
  push_cast
  rw [Int.toNat_of_nonneg g0, Int.toNat_of_nonneg (by rw [← e1]; exact h0)]
  ring

/-- The density increment iteration: after `m` steps the density has grown by `λ^m`, as long
as `log N ≥ W^m`. -/
theorem iter_claim (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) {k : ℕ} (hk : 3 ≤ k) {CI CS : ℝ}
    (hCI : 0 < CI) (hCS : 0 < CS) (hI : InvWith Str (k - 2) CI) (hS : SchmidtWith Str CS)
    {C : ℝ} (hC : 1 ≤ C)
    (hpar : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 2 * pV k CI CS δ ≤ qp C (1 / δ) ∧
      2 * pV k CI CS δ * Real.log (pB k CI CS δ) ≤ qp C (1 / δ))
    {δ0 : ℝ} (hδ0 : 0 < δ0) :
    ∀ m : ℕ, ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → A.Nonempty → ¬ Erdos142.HasAP k A →
      δ0 ≤ A.card / N → qp C (1 / δ0) ^ m ≤ Real.log N →
      (1 + cpK k / 2) ^ m * (A.card / N) ≤ 1 := by
  intro m
  induction m with
  | zero =>
    intro N A hA _ _ _ _
    rw [pow_zero, one_mul]
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    rw [div_le_one (by exact_mod_cast h)]
    have := Finset.card_le_card hA; simp at this; exact_mod_cast this
  | succ m ih =>
    intro N A hA hne hfree hδ hlog
    have hNpos : 0 < N := by
      obtain ⟨x, hx⟩ := hne
      have := Finset.mem_Icc.mp (hA hx); omega
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hAc : (0 : ℝ) < A.card := by exact_mod_cast hne.card_pos
    have hAN : (A.card : ℝ) ≤ N := by
      have := Finset.card_le_card hA; simp at this; exact_mod_cast this
    set δ : ℝ := A.card / N with hδdef
    have hδpos : 0 < δ := by positivity
    have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hNr]; exact hAN
    have hk1 : 1 ≤ k := by omega
    have hX : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδpos]; linarith
    have hXX : 1 / δ ≤ 1 / δ0 := one_div_le_one_div_of_le hδ0 hδ
    set W := qp C (1 / δ0) with hWdef
    have hW1 : 1 ≤ W := one_le_qp (by linarith) (hX.trans hXX)
    have hWδ : qp C (1 / δ) ≤ W := qp_mono (by linarith) hX hXX
    have hWlog : W ≤ Real.log N := (le_self_pow₀ hW1 (by omega)).trans hlog
    obtain ⟨h1, h2⟩ := hpar δ hδpos hδ1
    set V := pV k CI CS δ with hVdef
    have hV : 0 < V := qp_pos _ _
    have hB := pB_pos hk1 hCI hCS hδpos hδ1
    have hlarge : pB k CI CS δ ≤ (N : ℝ) ^ (1 / (2 * V)) := by
      rw [← Real.exp_log hB, Real.rpow_def_of_pos hNr, Real.exp_le_exp, mul_one_div,
        le_div_iff₀ (by positivity)]
      linarith
    obtain ⟨a, d, M, hd, hM, hsub, hinc⟩ :=
      dens_incr_explicit Str hk hCI hCS hI hS hA hne hfree hlarge
    set A' := rescale A a d M with hA'
    have hcard := rescale_card A a hd M
    rw [← hA'] at hcard
    have hM1 : (1 : ℝ) ≤ M := le_trans (Real.one_le_rpow hN1 (by positivity)) hM
    have hMr : (0 : ℝ) < M := by linarith
    have hcp : 0 < cpK k := by unfold cpK; positivity
    set lam := 1 + cpK k / 2 with hlam
    have hlam1 : 1 ≤ lam := by linarith
    have hinc' : lam * δ * M ≤ A'.card := by rw [hcard]; exact hinc
    have hA'pos : (0 : ℝ) < A'.card := lt_of_lt_of_le (by positivity) hinc'
    have hne' : A'.Nonempty := by
      rw [← Finset.card_pos]; exact_mod_cast hA'pos
    have hdens : lam * δ ≤ A'.card / M := by rw [le_div_iff₀ hMr]; exact hinc'
    have hδ0' : δ0 ≤ A'.card / M := by
      have : δ ≤ lam * δ := le_mul_of_one_le_left hδpos.le hlam1
      linarith
    have hlogM : W ^ m ≤ Real.log M := by
      have e1 : Real.log N / (2 * V) ≤ Real.log M := by
        have := Real.log_le_log (by positivity) hM
        rwa [Real.log_rpow hNr, one_div_mul_eq_div] at this
      have e2 : Real.log N / W ≤ Real.log N / (2 * V) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (h1.trans hWδ)
      have e3 : W ^ m ≤ Real.log N / W := by
        rw [le_div_iff₀ (by linarith), ← pow_succ]; exact hlog
      linarith
    have := ih M A' (rescale_subset A a d M) hne' (rescale_free hk1 hd hfree) hδ0' hlogM
    calc lam ^ (m + 1) * δ = lam ^ m * (lam * δ) := by ring
      _ ≤ lam ^ m * (A'.card / M) := mul_le_mul_of_nonneg_left hdens (by positivity)
      _ ≤ 1 := this

end

end LSS

end LSSFile_Reduction

section LSSFile_Final



/-!
# The Leng–Sah–Sawhney bound from the two structural hypotheses
-/

open Finset

namespace LSS

noncomputable section

/-- A progression with positive difference and `k > 1` terms is a progression in the sense of
`Erdos142.IsAPOfLength`. -/
theorem not_isAPOfLengthFree_of_hasAP (k : ℕ) (hk : 1 < k) (S : Finset ℕ)
    (h : Erdos142.HasAP k S) : ¬ Erdos142.IsAPOfLengthFree (S : Set ℕ) k := by
  obtain ⟨a, d, hd, h⟩ := h
  intro hfree
  have hinj : Function.Injective (fun n : ℕ => a + n * d) := by
    intro x y hxy
    simp only at hxy
    exact Nat.eq_of_mul_eq_mul_right hd (by omega : x * d = y * d)
  refine absurd (hfree _ ?_ ⟨a, d, ?_, rfl⟩) ?_
  · rintro x ⟨n, hn, rfl⟩
    rw [smul_eq_mul]
    exact h n (by exact_mod_cast hn)
  · rw [ENat.card_coe_set_eq]
    have : {x | ∃ (n : ℕ) (_ : (n : ℕ∞) < (k : ℕ∞)), a + n • d = x} =
        (((Finset.range k).image (fun n : ℕ => a + n * d) : Finset ℕ) : Set ℕ) := by
      ext x
      simp only [Set.mem_setOf_eq, Finset.coe_image, Finset.coe_range, Set.mem_image,
        Set.mem_Iio, smul_eq_mul, Nat.cast_lt, exists_prop]
    rw [this, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  · intro hle
    have : k ≤ 1 := by exact_mod_cast hle
    omega

/-- `r k N` is attained by a progression-free set. -/
theorem exists_r_set (k N : ℕ) (hk : 1 < k) :
    ∃ S : Finset ℕ, S ⊆ Icc 1 N ∧ ¬ Erdos142.HasAP k S ∧ Erdos142.r k N = S.card := by
  have hne : {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x}.Nonempty :=
    ⟨0, ∅, by simp, by simpa using Erdos142.isAPOfLengthFree_empty (α := ℕ) k, rfl⟩
  have hbdd : BddAbove {x | ∃ (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 N)
      (_ : Erdos142.IsAPOfLengthFree (S : Set ℕ) k), S.card = x} := by
    refine ⟨N, ?_⟩
    rintro m ⟨T, hT, -, rfl⟩
    simpa using (Finset.card_le_card hT).trans_eq (by simp)
  obtain ⟨S, hS, hfree, hcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨S, hS, fun h => not_isAPOfLengthFree_of_hasAP k hk S h hfree,
    by rw [Erdos142.r, ← hcard]⟩

/-- The core bound: a progression-free set of density `δ` in `{1, …, N}` has
`log log N < K (1 + log (1/δ))^D`. -/
theorem core_loglog (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) {k : ℕ} (hk : 3 ≤ k)
    (hI : InvHyp Str (k - 2)) (hS : SchmidtHyp Str) :
    ∃ K D : ℝ, 1 ≤ K ∧ 1 ≤ D ∧ ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → A.Nonempty →
      ¬ Erdos142.HasAP k A →
      Real.log (Real.log N) < K * (1 + Real.log (N / A.card)) ^ D := by
  obtain ⟨CI, hCI, hI⟩ := hI
  obtain ⟨CS, hCS, hS⟩ := hS
  have hk1 : 1 ≤ k := by omega
  obtain ⟨C, hC, hpar⟩ := param_bounds hk1 hCI hCS
  have hcp : 0 < cpK k := by unfold cpK; positivity
  set lam := 1 + cpK k / 2 with hlam
  have hlam1 : 1 < lam := by linarith
  set L := Real.log lam with hL
  have hL0 : 0 < L := Real.log_pos hlam1
  refine ⟨(1 / L + 1) * C, C + 1, ?_, by linarith, ?_⟩
  · have h0 : 0 < 1 / L := by positivity
    have : 1 ≤ 1 / L + 1 := by linarith
    nlinarith
  intro N A hA hne hfree
  have hNpos : 0 < N := by
    obtain ⟨x, hx⟩ := hne
    have := Finset.mem_Icc.mp (hA hx); omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hne.card_pos
  have hAN : (A.card : ℝ) ≤ N := by
    have := Finset.card_le_card hA; simp at this; exact_mod_cast this
  set δ : ℝ := A.card / N with hδdef
  have hδpos : 0 < δ := by positivity
  set X : ℝ := N / A.card with hXdef
  have hXδ : 1 / δ = X := by rw [hδdef, hXdef, one_div_div]
  have hX1 : 1 ≤ X := by rw [hXdef, le_div_iff₀ hAc]; linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  set ℓ := 1 + Real.log X with hℓ
  have hℓ1 : 1 ≤ ℓ := by linarith
  set m : ℕ := ⌊Real.log X / L⌋₊ + 1 with hm
  have hmgt : Real.log X / L < m := by rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hmle : (m : ℝ) ≤ ℓ / L + ℓ := by
    have : (⌊Real.log X / L⌋₊ : ℝ) ≤ Real.log X / L := Nat.floor_le (by positivity)
    have : Real.log X / L ≤ ℓ / L := div_le_div_of_nonneg_right (by linarith) hL0.le
    rw [hm]; push_cast; linarith
  -- after `m` steps the density would exceed `1`
  have hlamm : 1 < lam ^ m * δ := by
    have e : lam ^ m = Real.exp (m * L) := by
      rw [hL, mul_comm, Real.exp_mul, Real.exp_log (by linarith)]; norm_cast
    have : Real.log X < m * L := by rwa [div_lt_iff₀ hL0] at hmgt
    have : X < lam ^ m := by
      rw [e]; calc X = Real.exp (Real.log X) := (Real.exp_log (by linarith)).symm
        _ < _ := Real.exp_lt_exp.mpr this
    have hXd : X * δ = 1 := by rw [← hXδ]; field_simp
    nlinarith
  have hW : Real.log N < qp C X ^ m := by
    by_contra hcon
    push_neg at hcon
    have := iter_claim Str hk hCI hCS hI hS hC hpar hδpos m N A hA hne hfree le_rfl
      (by rw [hXδ]; exact hcon)
    linarith
  have hRHS : 0 < (1 / L + 1) * C * ℓ ^ (C + 1) := by positivity
  rcases (Real.log_nonneg hN1).eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]; exact hRHS
  have hlog : Real.log (Real.log N) < m * (C * ℓ ^ C) := by
    have := Real.log_lt_log hpos hW
    rwa [Real.log_pow, qp, Real.log_exp] at this
  have hℓC : 0 ≤ C * ℓ ^ C := by positivity
  calc Real.log (Real.log N) < m * (C * ℓ ^ C) := hlog
    _ ≤ (ℓ / L + ℓ) * (C * ℓ ^ C) := mul_le_mul_of_nonneg_right hmle hℓC
    _ = (1 / L + 1) * C * (ℓ ^ C * ℓ) := by ring
    _ = (1 / L + 1) * C * ℓ ^ (C + 1) := by rw [Real.rpow_add_one (by linarith)]

lemma final_numeric {K D t : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D) (ht : 2 * K ≤ t) :
    K * (2 * t) ^ D ≤ t ^ (2 * D) := by
  have ht0 : 0 < t := by linarith
  have h1 : (2 * t) ^ D = 2 ^ D * t ^ D := Real.mul_rpow (by norm_num) ht0.le
  have h2 : t ^ (2 * D) = t ^ D * t ^ D := by rw [two_mul, Real.rpow_add ht0]
  have h3 : (2 * K) ^ D ≤ t ^ D := Real.rpow_le_rpow (by linarith) ht (by linarith)
  have h4 : (2 * K) ^ D = 2 ^ D * K ^ D := Real.mul_rpow (by norm_num) (by linarith)
  have h5 : K ≤ K ^ D := by
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
      _ ≤ K ^ D := Real.rpow_le_rpow_of_exponent_le hK hD
  have h6 : 0 ≤ 2 ^ D * t ^ D := by positivity
  rw [h1, h2]
  calc K * (2 ^ D * t ^ D) ≤ K ^ D * (2 ^ D * t ^ D) := mul_le_mul_of_nonneg_right h5 h6
    _ = (2 * K) ^ D * t ^ D := by rw [h4]; ring
    _ ≤ t ^ D * t ^ D := mul_le_mul_of_nonneg_right h3 (by positivity)

/-- **Leng–Sah–Sawhney, conditional form.** For `k ≥ 3`, the quasi-polynomial inverse theorem for
the `U^{k-1}` norm together with the Schmidt-type equidistribution property of the structured
functions imply `r_k(N) ≤ N exp (-(log log N)^c)` for large `N`. -/
theorem lss_of_hyps (Str : ℕ → ℝ → (ℤ → ℝ) → Prop) {k : ℕ} (hk : 3 ≤ k)
    (hI : InvHyp Str (k - 2)) (hS : SchmidtHyp Str) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r k N : ℝ) ≤ N * Real.exp (-(Real.log (Real.log N)) ^ c) := by
  obtain ⟨K, D, hK, hD, hcore⟩ := core_loglog Str hk hI hS
  have hD0 : 0 < D := by linarith
  refine ⟨1 / (2 * D), by positivity, ?_⟩
  set Y0 : ℝ := (2 * K) ^ (2 * D) with hY0
  rw [Filter.eventually_atTop]
  refine ⟨⌈Real.exp (Real.exp Y0)⌉₊ + 1, fun N hN => ?_⟩
  have hNr : Real.exp (Real.exp Y0) < N := by
    have := Nat.le_ceil (Real.exp (Real.exp Y0))
    have : (⌈Real.exp (Real.exp Y0)⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    linarith
  have hN0 : (0 : ℝ) < N := lt_trans (Real.exp_pos _) hNr
  have hlogN : Real.exp Y0 < Real.log N := by
    rw [Real.lt_log_iff_exp_lt hN0]; exact hNr
  have hlogN0 : 0 < Real.log N := lt_trans (Real.exp_pos _) hlogN
  set y := Real.log (Real.log N) with hy
  have hyY : Y0 < y := by rw [hy, Real.lt_log_iff_exp_lt hlogN0]; exact hlogN
  have hY00 : 0 < Y0 := by positivity
  have hy0 : 0 < y := by linarith
  set t := y ^ (1 / (2 * D)) with ht
  have ht0 : 0 < t := by positivity
  have hty : t ^ (2 * D) = y := by
    rw [ht, ← Real.rpow_mul hy0.le]; field_simp; exact Real.rpow_one y
  have h2Kt : 2 * K ≤ t := by
    have : Y0 ^ (1 / (2 * D)) ≤ t := Real.rpow_le_rpow hY00.le hyY.le (by positivity)
    rwa [hY0, ← Real.rpow_mul (by linarith), mul_one_div_cancel (by positivity),
      Real.rpow_one] at this
  obtain ⟨S, hS, hfree, hr⟩ := exists_r_set k N (by omega)
  rw [hr]
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; positivity
  by_contra hbig
  push_neg at hbig
  have hSc : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hX : Real.log (N / S.card) < t := by
    rw [Real.log_lt_iff_lt_exp (by positivity), div_lt_iff₀ hSc]
    have e : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have : (N : ℝ) * Real.exp (-t) * Real.exp t < S.card * Real.exp t :=
      mul_lt_mul_of_pos_right hbig (Real.exp_pos _)
    nlinarith
  have hc := hcore N S hS hSne hfree
  rw [← hy] at hc
  have hℓ : 1 + Real.log (N / S.card) ≤ 2 * t := by linarith
  have hℓ0 : 0 ≤ 1 + Real.log (N / S.card) := by
    have : 1 ≤ (N : ℝ) / S.card := by
      rw [le_div_iff₀ hSc]
      have := Finset.card_le_card hS; simp at this; exact_mod_cast (by linarith)
    have := Real.log_nonneg this; linarith
  have h1 : K * (1 + Real.log (N / S.card)) ^ D ≤ K * (2 * t) ^ D :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hℓ0 hℓ hD0.le) (by linarith)
  have h2 := final_numeric hK hD h2Kt
  rw [hty] at h2
  linarith

end

end LSS

end LSSFile_Final

theorem solution (k : ℕ) (hk : 5 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (Erdos142.r k N : ℝ) ≤ (N : ℝ) * Real.exp (-(Real.log (Real.log N)) ^ c) := by
  obtain ⟨Str, hI, hS⟩ := LSS.structured_inverse_and_schmidt (k - 2) (by omega)
  exact LSS.lss_of_hyps Str (by omega) hI hS
