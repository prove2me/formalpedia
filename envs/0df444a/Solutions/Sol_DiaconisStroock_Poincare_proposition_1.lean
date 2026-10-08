-- Prove2me | solution 1 for DiaconisStroock.Poincare.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T07:33:21.535005+00:00
-- url     : https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_DiaconisStroock_Poincare_Kappa
import Definitions.Def_mm_spectral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Definitions.Def_mm_basic
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.Tactic.Push
import Mathlib.Tactic
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_Poincare_Paths


open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem MarkovMixing.spectral_representation {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  classical
  -- the symmetrising square roots
  set sq : V → ℝ := fun x => Real.sqrt (π x) with hsqdef
  have hsqpos : ∀ x : V, 0 < sq x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hsqne : ∀ x : V, sq x ≠ 0 := fun x => ne_of_gt (hsqpos x)
  have hsqsq : ∀ x : V, sq x * sq x = π x := fun x =>
    Real.mul_self_sqrt (le_of_lt (hpos x))
  -- the symmetrised matrix
  set A : Matrix V V ℝ := fun x y => sq x * P x y / sq y with hAdef
  have hAval : ∀ x y : V, A x y = sq x * P x y / sq y := fun _ _ => rfl
  have hAsymm : ∀ x y : V, A x y = A y x := by
    intro x y
    rw [hAval, hAval, div_eq_div_iff (hsqne y) (hsqne x)]
    have h1 : sq x * sq x * P x y = sq y * sq y * P y x := by
      rw [hsqsq, hsqsq]; exact hrev x y
    calc sq x * P x y * sq x = sq x * sq x * P x y := by ring
      _ = sq y * sq y * P y x := h1
      _ = sq y * P y x * sq y := by ring
  have hAh : A.IsHermitian := by
    ext x y
    rw [Matrix.conjTranspose_apply, star_trivial]
    exact hAsymm y x
  -- the eigenvector matrix
  set U : Matrix V V ℝ := (hAh.eigenvectorUnitary : Matrix V V ℝ) with hUdef
  have hUcol : ∀ j x : V, U x j = (hAh.eigenvectorBasis j) x := fun j x => rfl
  have hUstar : ∀ i j : V, (star U) i j = U j i := by
    intro i j
    rw [Matrix.star_apply, star_trivial]
  have hUU : ∀ j k : V, ∑ x, U x j * U x k = if j = k then (1 : ℝ) else 0 := by
    intro j k
    have h : (star U : Matrix V V ℝ) * U = 1 := by
      rw [hUdef]
      exact_mod_cast (Unitary.coe_star_mul_self hAh.eigenvectorUnitary)
    have h2 := congrFun (congrFun h j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun x _ => by rw [hUstar]
  have hUU' : ∀ x y : V, ∑ j, U x j * U y j = if x = y then (1 : ℝ) else 0 := by
    intro x y
    have h : U * (star U : Matrix V V ℝ) = 1 := by
      rw [hUdef]
      exact_mod_cast (Unitary.coe_mul_star_self hAh.eigenvectorUnitary)
    have h2 := congrFun (congrFun h x) y
    rw [Matrix.mul_apply, Matrix.one_apply] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun j _ => by rw [hUstar]
  -- the eigenvalue equation for `A`, in coordinates
  have hAU : ∀ (j x : V), ∑ y, A x y * U y j = hAh.eigenvalues j * U x j := by
    intro j x
    have h := hAh.mulVec_eigenvectorBasis j
    have h2 := congrFun h x
    simpa [Matrix.mulVec, dotProduct, hUcol] using h2
  -- powers of `A` are the conjugated powers of `P`
  have hApow : ∀ (t : ℕ) (x y : V), (A ^ t) x y = sq x * (P ^ t) x y / sq y := by
    intro t
    induction t with
    | zero =>
        intro x y
        rw [pow_zero, pow_zero, Matrix.one_apply]
        by_cases hxy : x = y
        · rw [if_pos hxy, hxy]
          rw [mul_one, div_self (hsqne y)]
        · rw [if_neg hxy]
          simp
    | succ n ih =>
        intro x y
        have hL : (A ^ (n + 1)) x y = ∑ z, (A ^ n) x z * A z y := by
          rw [pow_succ]; rfl
        have hR : (P ^ (n + 1)) x y = ∑ z, (P ^ n) x z * P z y := by
          rw [pow_succ]; rfl
        rw [hL, hR, Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [ih x z, hAval]
        field_simp [hsqne z, hsqne y]
  -- transport everything to the index type `Fin (Fintype.card V)`
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with hedef
  refine ⟨fun j => hAh.eigenvalues (e j), fun j x => U x (e j) / sq x, ?_, ?_, ?_⟩
  · -- eigenfunctions of `P`
    intro j
    funext x
    have h := hAU (e j) x
    have hstep : ∑ y, P x y * (U y (e j) / sq y) = (∑ y, A x y * U y (e j)) / sq x := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hAval]
      field_simp [hsqne x, hsqne y]
    show ∑ y, P x y * (U y (e j) / sq y) = hAh.eigenvalues (e j) * (U x (e j) / sq x)
    rw [hstep, h]
    field_simp [hsqne x]
  · -- orthonormality in `ℓ²(π)`
    intro j k
    unfold innerPi
    have hterm : ∀ x : V,
        (U x (e j) / sq x) * (U x (e k) / sq x) * π x = U x (e j) * U x (e k) := by
      intro x
      rw [← hsqsq x]
      field_simp [hsqne x]
    rw [Finset.sum_congr rfl fun x _ => hterm x, hUU (e j) (e k)]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos (by rw [hjk])]
    · rw [if_neg hjk, if_neg (fun hc => hjk (e.injective hc))]
  · -- the spectral decomposition of the transition probabilities
    intro t x y
    -- first: the decomposition of `A ^ t`
    have hpowU : ∀ (t : ℕ) (j x : V),
        ∑ y, (A ^ t) x y * U y j = hAh.eigenvalues j ^ t * U x j := by
      intro t
      induction t with
      | zero =>
          intro j x
          rw [pow_zero, pow_zero, one_mul]
          rw [Finset.sum_eq_single x]
          · rw [Matrix.one_apply_eq, one_mul]
          · intro z _ hz
            rw [Matrix.one_apply_ne (Ne.symm hz), zero_mul]
          · intro hc; exact absurd (Finset.mem_univ x) hc
      | succ n ih =>
          intro j x
          have hL : ∀ z : V, (A ^ (n + 1)) x z = ∑ w, A x w * (A ^ n) w z := by
            intro z
            rw [pow_succ']
            rfl
          rw [Finset.sum_congr rfl fun z _ => by rw [hL z, Finset.sum_mul]]
          rw [Finset.sum_comm]
          have hinner : ∀ w : V, ∑ z, A x w * (A ^ n) w z * U z j
              = A x w * (hAh.eigenvalues j ^ n * U w j) := by
            intro w
            rw [← ih j w, Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
          rw [Finset.sum_congr rfl fun w _ => hinner w]
          have : ∑ w, A x w * (hAh.eigenvalues j ^ n * U w j)
              = hAh.eigenvalues j ^ n * ∑ w, A x w * U w j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun w _ => by ring
          rw [this, hAU j x, pow_succ]
          ring
    have hAt : (A ^ t) x y = ∑ v : V, hAh.eigenvalues v ^ t * (U x v * U y v) := by
      have hexpand : ∑ v : V, hAh.eigenvalues v ^ t * (U x v * U y v)
          = ∑ v : V, ∑ z, U y v * ((A ^ t) x z * U z v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum, hpowU t v x]
        ring
      rw [hexpand, Finset.sum_comm]
      have hcollapse : ∀ z : V, ∑ v, U y v * ((A ^ t) x z * U z v)
          = (A ^ t) x z * (if z = y then (1 : ℝ) else 0) := by
        intro z
        rw [← hUU' z y]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ => by ring
      rw [Finset.sum_congr rfl fun z _ => hcollapse z, Finset.sum_eq_single y]
      · rw [if_pos rfl, mul_one]
      · intro z _ hz
        rw [if_neg hz, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ y) hc
    -- now convert to `P`
    have hdiv : (P ^ t) x y / π y = (A ^ t) x y / (sq x * sq y) := by
      rw [hApow t x y, ← hsqsq y]
      field_simp [hsqne x, hsqne y]
    rw [hdiv, hAt]
    rw [← Equiv.sum_comp e (fun v : V => hAh.eigenvalues v ^ t * (U x v * U y v))]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hsqne x, hsqne y]

#print axioms MarkovMixing.spectral_representation


open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.harmonic_eq_const {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (h : V → ℝ) (hh : Harmonic P h) (x y : V) :
    h x = h y := by
  haveI : Nonempty V := ⟨x⟩
  have hpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hpow_row : ∀ (t : ℕ) (a : V), ∑ b, (P ^ t) a b = 1 := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ n * P) a b = ∑ z, (P ^ n) a z * P z b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun z _ => by rw [← Finset.mul_sum, hP.2 z, mul_one]]
        exact ih a
  have hharm_pow : ∀ (t : ℕ) (a : V), h a = ∑ b, (P ^ t) a b * h b := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have hmul : ∀ z : V, (P ^ n * P) a z = ∑ b, (P ^ n) a b * P b z := fun z => rfl
        rw [Finset.sum_congr rfl fun z _ => by rw [hmul z]]
        have expand : ∑ z, (∑ b, (P ^ n) a b * P b z) * h z
            = ∑ b, (P ^ n) a b * ∑ z, P b z * h z := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => by ring
        rw [expand]
        rw [ih a]
        exact Finset.sum_congr rfl fun b _ => by rw [← hh b]
  obtain ⟨x₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) h Finset.univ_nonempty
  have hmax' : ∀ z : V, h z ≤ h x₀ := fun z => hmax z (Finset.mem_univ z)
  have key : ∀ (t : ℕ) (z : V), 0 < (P ^ t) x₀ z → h z = h x₀ := by
    intro t z hz
    have hle : ∀ b ∈ (Finset.univ : Finset V),
        (P ^ t) x₀ b * h b ≤ (P ^ t) x₀ b * h (x₀) :=
      fun b _ => mul_le_mul_of_nonneg_left (hmax' b) (hpow_nonneg t x₀ b)
    have hEq : ∑ b, (P ^ t) x₀ b * h b = ∑ b, (P ^ t) x₀ b * h x₀ := by
      rw [← hharm_pow t x₀, ← Finset.sum_mul, hpow_row t x₀, one_mul]
    have hptw := (Finset.sum_eq_sum_iff_of_le hle).mp hEq z (Finset.mem_univ z)
    exact mul_left_cancel₀ hz.ne' hptw
  obtain ⟨t₁, ht₁⟩ := hirr x₀ x
  obtain ⟨t₂, ht₂⟩ := hirr x₀ y
  rw [key t₁ x ht₁, key t₂ y ht₂]

#print axioms MarkovMixing.harmonic_eq_const


open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.exists_pow_pos {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : Aperiodic P) :
    ∃ r : ℕ, 0 < r ∧ ∀ x y : V, 0 < (P ^ r) x y := by
  classical
  have hpow_nonneg : ∀ (s : ℕ) (a b : V), 0 ≤ (P ^ s) a b := by
    intro s
    induction s with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hchain : ∀ (a b : ℕ) (u v w : V),
      (P ^ a) u v * (P ^ b) v w ≤ (P ^ (a + b)) u w := by
    intro a b u v w
    have hsum : (P ^ (a + b)) u w = ∑ z, (P ^ a) u z * (P ^ b) z w := by
      rw [pow_add]; rfl
    rw [hsum]
    exact Finset.single_le_sum (f := fun z => (P ^ a) u z * (P ^ b) z w)
      (fun z _ => mul_nonneg (hpow_nonneg a u z) (hpow_nonneg b z w)) (Finset.mem_univ v)
  -- return sets are nonempty and closed under addition
  have hret_ne : ∀ a : V, ∃ t₀, t₀ ∈ returnSet P a := by
    intro a
    obtain ⟨b, -, hb⟩ : ∃ b ∈ (Finset.univ : Finset V), 0 < P a b := by
      by_contra hcon
      push_neg at hcon
      have hle : ∑ b, P a b ≤ 0 := Finset.sum_nonpos fun b hb => hcon b hb
      rw [hP.2 a] at hle
      linarith
    obtain ⟨s, hs⟩ := hirr b a
    refine ⟨1 + s, ⟨by omega, ?_⟩⟩
    have h1 : (P ^ 1) a b * (P ^ s) b a ≤ (P ^ (1 + s)) a a := hchain 1 s a b a
    have hpb : (0:ℝ) < (P ^ 1) a b := by simpa [pow_one] using hb
    nlinarith [mul_pos hpb hs]
  have hret_add : ∀ (a : V) (s t : ℕ), s ∈ returnSet P a → t ∈ returnSet P a →
      s + t ∈ returnSet P a := by
    intro a s t hs ht
    have hs1 := hs.1
    have ht1 := ht.1
    refine ⟨by omega, ?_⟩
    have h1 := hchain s t a a a
    nlinarith [mul_pos hs.2 ht.2]
  -- aperiodicity says the gcd of the return set is one
  have hgcd : ∀ a : V, Nat.setGcd (returnSet P a) = 1 := by
    intro a
    obtain ⟨t₀, ht₀⟩ := hret_ne a
    have hg_dvd : Nat.setGcd (returnSet P a) ∣ t₀ := Nat.setGcd_dvd_of_mem ht₀
    have hgpos : 0 < Nat.setGcd (returnSet P a) := by
      rcases Nat.eq_zero_or_pos (Nat.setGcd (returnSet P a)) with h | h
      · rw [h] at hg_dvd
        have h0 := Nat.eq_zero_of_zero_dvd hg_dvd
        have h1 := ht₀.1
        omega
      · exact h
    have hset : {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t}
        = {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} := by
      ext d
      simp only [Set.mem_setOf_eq]
      exact Nat.dvd_setGcd_iff.symm
    have hsup : sSup {d : ℕ | ∀ t ∈ returnSet P a, d ∣ t} = Nat.setGcd (returnSet P a) := by
      rw [hset]
      have hne : ({d : ℕ | d ∣ Nat.setGcd (returnSet P a)}).Nonempty :=
        ⟨Nat.setGcd (returnSet P a), dvd_rfl⟩
      have hbd : BddAbove {d : ℕ | d ∣ Nat.setGcd (returnSet P a)} :=
        ⟨Nat.setGcd (returnSet P a), fun d hd => Nat.le_of_dvd hgpos hd⟩
      refine le_antisymm (csSup_le hne fun d hd => Nat.le_of_dvd hgpos hd)
        (le_csSup hbd dvd_rfl)
    have := hap a
    rw [period, hsup] at this
    exact this
  -- every sufficiently large integer is a return time
  have hbig : ∀ a : V, ∃ N : ℕ, ∀ m : ℕ, N ≤ m → 1 ≤ m → m ∈ returnSet P a := by
    intro a
    obtain ⟨N, hN⟩ := Nat.exists_mem_closure_of_ge (s := returnSet P a)
    refine ⟨N, fun m hm hm1 => ?_⟩
    have hmem : m ∈ AddSubmonoid.closure (returnSet P a) := by
      refine hN m hm ?_
      rw [hgcd a]
      exact one_dvd m
    have hQ : ∀ k : ℕ, k ∈ AddSubmonoid.closure (returnSet P a) →
        k = 0 ∨ k ∈ returnSet P a := by
      intro k hk
      induction hk using AddSubmonoid.closure_induction with
      | mem z hz => exact Or.inr hz
      | zero => exact Or.inl rfl
      | add u v _ _ ihu ihv =>
          rcases ihu with rfl | hu
          · simpa using ihv
          · rcases ihv with rfl | hv
            · simpa using Or.inr hu
            · exact Or.inr (hret_add a u v hu hv)
    rcases hQ m hmem with h | h
    · omega
    · exact h
  choose N hN using hbig
  choose r hr using hirr
  refine ⟨(Finset.univ.sup N) + (Finset.univ.sup fun x => Finset.univ.sup fun y => r x y) + 1,
    by omega, ?_⟩
  intro x y
  set Nm := Finset.univ.sup N with hNm
  set Rm := Finset.univ.sup fun x => Finset.univ.sup fun y => r x y with hRm
  have hrle : r x y ≤ Rm := by
    refine le_trans ?_ (Finset.le_sup (f := fun x => Finset.univ.sup fun y => r x y)
      (Finset.mem_univ x))
    exact Finset.le_sup (f := fun y => r x y) (Finset.mem_univ y)
  have hNle : N x ≤ Nm := Finset.le_sup (Finset.mem_univ x)
  have hsplit : Nm + Rm + 1 = (Nm + Rm + 1 - r x y) + r x y := by omega
  have hmem : (Nm + Rm + 1 - r x y) ∈ returnSet P x :=
    hN x _ (by omega) (by omega)
  have hbound := hchain (Nm + Rm + 1 - r x y) (r x y) x x y
  rw [← hsplit] at hbound
  have := mul_pos hmem.2 (hr x y)
  linarith

#print axioms MarkovMixing.exists_pow_pos


open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem MarkovMixing.eigenvalue_basic {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) :
    (∀ lam : ℝ, IsEigenvalue P lam → |lam| ≤ 1) ∧
    (MarkovMixing.Irreducible P → ∀ f : V → ℝ, P.mulVec f = f → ∀ x y : V, f x = f y) ∧
    (MarkovMixing.Irreducible P → Aperiodic P → ¬ IsEigenvalue P (-1)) := by
  classical
  have hpow_nonneg : ∀ (n : ℕ) (a b : V), 0 ≤ (P ^ n) a b := by
    intro n
    induction n with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ m ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (ih a w) (hP.1 w b)
  have hpow_row : ∀ (n : ℕ) (a : V), ∑ b, (P ^ n) a b = 1 := by
    intro n
    induction n with
    | zero => intro a; simp [Matrix.one_apply]
    | succ m ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ m * P) a b = ∑ w, (P ^ m) a w * P w b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum, hP.2 w, mul_one]]
        exact ih a
  refine ⟨?_, ?_, ?_⟩
  · -- (i) every eigenvalue has modulus at most one
    rintro lam ⟨f, hfne, hf⟩
    obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hfne (funext hcon)
    haveI : Nonempty V := ⟨z⟩
    obtain ⟨x₀, -, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset V) (fun x => |f x|) Finset.univ_nonempty
    have hmax' : ∀ w : V, |f w| ≤ |f x₀| := fun w => hmax w (Finset.mem_univ w)
    have hx₀pos : 0 < |f x₀| :=
      lt_of_lt_of_le (abs_pos.mpr hz) (hmax' z)
    have hval : lam * f x₀ = ∑ y, P x₀ y * f y := by
      have h := congrFun hf x₀
      show lam * f x₀ = (P.mulVec f) x₀
      rw [h]
      simp [Pi.smul_apply, smul_eq_mul]
    have hbound : |lam| * |f x₀| ≤ |f x₀| := by
      rw [← abs_mul, hval]
      calc |∑ y, P x₀ y * f y| ≤ ∑ y, |P x₀ y * f y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, P x₀ y * |f x₀| := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_of_nonneg (hP.1 x₀ y)]
            exact mul_le_mul_of_nonneg_left (hmax' y) (hP.1 x₀ y)
        _ = |f x₀| := by rw [← Finset.sum_mul, hP.2 x₀, one_mul]
    nlinarith [hbound, hx₀pos]
  · -- (ii) eigenfunctions of eigenvalue one are constant
    intro hirr f hf x y
    have hharm : Harmonic P f := by
      intro w
      have h := congrFun hf w
      exact h.symm
    exact MarkovMixing.harmonic_eq_const P hP hirr f hharm x y
  · -- (iii) `-1` is not an eigenvalue of an irreducible aperiodic chain
    rintro hirr hap ⟨f, hfne, hf⟩
    have hfneg : P.mulVec f = -f := by
      rw [hf]
      funext w
      simp
    rcases isEmpty_or_nonempty V with hV | hV
    · exact hfne (funext fun w => (IsEmpty.false w).elim)
    obtain ⟨r, hr0, hrpos⟩ := MarkovMixing.exists_pow_pos P hP hirr hap
    -- the doubled power is positive and fixes `f`
    set R : ℕ := 2 * r with hR
    have hRpos : ∀ x y : V, 0 < (P ^ R) x y := by
      intro x y
      have hsplit : (P ^ R) x y = ∑ z, (P ^ r) x z * (P ^ r) z y := by
        rw [hR, two_mul, pow_add]; rfl
      rw [hsplit]
      refine Finset.sum_pos (fun z _ => mul_pos (hrpos x z) (hrpos z y)) ?_
      exact ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    have hiter : ∀ n : ℕ, (P ^ n).mulVec f = ((-1 : ℝ) ^ n) • f := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, ← Matrix.mulVec_mulVec, hfneg]
          have : (P ^ m).mulVec (-f) = -((P ^ m).mulVec f) := by
            funext w
            show ∑ y, (P ^ m) w y * (-f y) = -∑ y, (P ^ m) w y * f y
            rw [← Finset.sum_neg_distrib]
            exact Finset.sum_congr rfl fun y _ => by ring
          rw [this, ih]
          funext w
          simp [pow_succ]
    have hfix : (P ^ R).mulVec f = f := by
      rw [hiter R, hR]
      have : ((-1 : ℝ) ^ (2 * r)) = 1 := by
        rw [pow_mul]
        norm_num
      rw [this, one_smul]
    -- `P ^ R` is stochastic and irreducible, so `f` is constant
    have hstochR : IsStochastic (P ^ R) := ⟨fun a b => hpow_nonneg R a b, hpow_row R⟩
    have hirrR : MarkovMixing.Irreducible (P ^ R) := by
      intro a b
      exact ⟨1, by rw [pow_one]; exact hRpos a b⟩
    have hharmR : Harmonic (P ^ R) f := by
      intro w
      exact (congrFun hfix w).symm
    have hconst : ∀ a b : V, f a = f b :=
      fun a b => MarkovMixing.harmonic_eq_const (P ^ R) hstochR hirrR f hharmR a b
    -- a constant eigenfunction of eigenvalue `-1` must vanish
    set x₀ : V := Classical.arbitrary V with hx₀
    have hcv : ∀ w : V, f w = f x₀ := fun w => hconst w x₀
    have hzero : f x₀ = - f x₀ := by
      have h := congrFun hfneg x₀
      show f x₀ = -f x₀
      have hlhs : (P.mulVec f) x₀ = f x₀ := by
        show ∑ y, P x₀ y * f y = f x₀
        rw [Finset.sum_congr rfl fun y _ => by rw [hcv y], ← Finset.sum_mul, hP.2 x₀, one_mul]
      rw [hlhs] at h
      simpa using h
    have : f x₀ = 0 := by linarith
    exact hfne (funext fun w => by rw [hcv w, this]; rfl)

#print axioms MarkovMixing.eigenvalue_basic


set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace DirichletGap

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma pow_entry_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P) :
    ∀ (t : ℕ) (x y : V), 0 ≤ (P ^ t) x y := by
  intro t
  induction t with
  | zero =>
    intro x y
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  | succ t ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hP.1 z y)

lemma vecMul_pow {P : Matrix V V ℝ} {π : V → ℝ} (hπ : IsStationary P π) :
    ∀ t : ℕ, Matrix.vecMul π (P ^ t) = π := by
  intro t
  induction t with
  | zero => simp
  | succ t ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

lemma pi_pos {P : Matrix V V ℝ} (hirr : MarkovMixing.Irreducible P) {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P) : ∀ x, 0 < π x := by
  obtain ⟨y, hy⟩ : ∃ y, 0 < π y := by
    by_contra hcon
    push_neg at hcon
    have h1 : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun i _ => hcon i
    have := hπ.1.2
    linarith
  intro x
  obtain ⟨t, ht⟩ := hirr y x
  have hv : ∑ z, π z * (P ^ t) z x = π x := congrFun (vecMul_pow hπ t) x
  have h2 : π y * (P ^ t) y x ≤ ∑ z, π z * (P ^ t) z x := by
    refine Finset.single_le_sum (f := fun z => π z * (P ^ t) z x) ?_ (Finset.mem_univ y)
    exact fun z _ => mul_nonneg (hπ.1.1 z) (pow_entry_nonneg hP t z x)
  have := mul_pos hy ht
  linarith

lemma innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g :=
  Finset.sum_congr rfl fun x _ => by ring

lemma dirichlet_eq_inner {P : Matrix V V ℝ} {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) (g : V → ℝ) :
    dirichletForm P π g = innerPi π g g - innerPi π g (P.mulVec g) := by
  have hrow : ∀ x, ∑ y, P x y = 1 := hP.2
  have hcol : ∀ y, ∑ x, π x * P x y = π y := fun y => congrFun hπ.2 y
  have A : ∑ x, ∑ y, (g x) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, hrow x, mul_one]
    ring
  have B : ∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y) = ∑ x : V, g x * g x * π x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hcol y]
    ring
  have C : ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y)
      = ∑ x : V, g x * (P.mulVec g) x * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (P.mulVec g) x = ∑ y, P x y * g y from rfl, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hall : ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y)
      = (∑ x : V, ∑ y : V, (g x) ^ 2 * (π x * P x y))
        + (∑ x : V, ∑ y : V, (g y) ^ 2 * (π x * P x y))
        - 2 * ∑ x : V, ∑ y : V, (g x * g y) * (π x * P x y) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  show 2⁻¹ * ∑ x : V, ∑ y : V, (g x - g y) ^ 2 * (π x * P x y) = _
  rw [hall, A, B, C]
  show _ = (∑ x : V, g x * g x * π x) - ∑ x : V, g x * (P.mulVec g) x * π x
  ring

section Spectral

variable {P : Matrix V V ℝ} {π : V → ℝ} {n : ℕ} {lam : Fin n → ℝ} {ff : Fin n → V → ℝ}

lemma completeness
    (hspec : ∀ (t : ℕ) (x y : V), (P ^ t) x y / π y = ∑ j, ff j x * ff j y * lam j ^ t)
    (x y : V) : ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y := by
  have h := hspec 0 x y
  simpa [Matrix.one_apply] using h.symm

lemma expand (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) : ∑ j, innerPi π g (ff j) * ff j x = g x := by
  have e1 : ∀ j, innerPi π g (ff j) * ff j x = ∑ y : V, g y * π y * (ff j y * ff j x) := by
    intro j
    show (∑ y : V, g y * ff j y * π y) * ff j x = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl (fun j _ => e1 j), Finset.sum_comm]
  have e2 : ∀ y : V, ∑ j, g y * π y * (ff j y * ff j x)
      = g y * π y * ((if y = x then 1 else 0) / π x) := by
    intro y
    rw [← Finset.mul_sum, hcomp y x]
  rw [Finset.sum_congr rfl (fun y _ => e2 y),
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x) (fun b _ hb => by simp [hb])]
  have hx := (hpos x).ne'
  field_simp
  simp

lemma norm_eq (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) : innerPi π g g = ∑ j, (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * g x * π x
      = ∑ j, innerPi π g (ff j) * (g x * ff j x * π x) := by
    intro x
    have : ∀ j, innerPi π g (ff j) * (g x * ff j x * π x)
        = (innerPi π g (ff j) * ff j x) * (g x * π x) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g x]
    ring
  show ∑ x : V, g x * g x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * innerPi π g (ff j) = _
  ring

lemma mulVec_expand (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) (x : V) :
    (P.mulVec g) x = ∑ j, innerPi π g (ff j) * lam j * ff j x := by
  have e1 : ∀ y : V, P x y * g y = ∑ j, innerPi π g (ff j) * (P x y * ff j y) := by
    intro y
    have : ∀ j, innerPi π g (ff j) * (P x y * ff j y)
        = (innerPi π g (ff j) * ff j y) * P x y := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul, expand hpos hcomp g y]
    ring
  show ∑ y : V, P x y * g y = _
  rw [Finset.sum_congr rfl (fun y _ => e1 y), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  have : ∑ y : V, P x y * ff j y = lam j * ff j x := by
    have := congrFun (heig j) x
    simpa [Matrix.mulVec, dotProduct] using this
  rw [this]
  ring

lemma inner_mulVec (heig : ∀ j, P.mulVec (ff j) = lam j • ff j) (hpos : ∀ x, 0 < π x)
    (hcomp : ∀ x y : V, ∑ j, ff j x * ff j y = (if x = y then 1 else 0) / π y)
    (g : V → ℝ) :
    innerPi π g (P.mulVec g) = ∑ j, lam j * (innerPi π g (ff j)) ^ 2 := by
  have e1 : ∀ x : V, g x * (P.mulVec g) x * π x
      = ∑ j, (innerPi π g (ff j) * lam j) * (g x * ff j x * π x) := by
    intro x
    rw [mulVec_expand heig hpos hcomp g x, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ x : V, g x * (P.mulVec g) x * π x = _
  rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  show innerPi π g (ff j) * lam j * innerPi π g (ff j) = _
  ring

end Spectral

end DirichletGap

open DirichletGap

theorem MarkovMixing.dirichlet_gap {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P)
    (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) :
    MarkovMixing.spectralGap P =
      sInf {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
        MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} ∧
    ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧ MarkovMixing.innerPi π f f = 1 ∧
      MarkovMixing.spectralGap P = MarkovMixing.dirichletForm P π f := by
  classical
  have hpos := pi_pos hirr hπ hP
  have hsum : ∑ x : V, π x = 1 := hπ.1.2
  obtain ⟨lam, ff, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := completeness hspec
  have hdir : ∀ g : V → ℝ, dirichletForm P π g
      = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
    intro g
    rw [dirichlet_eq_inner hP hπ g, norm_eq hpos hcomp g, inner_mulVec heig hpos hcomp g,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcoef : ∀ (a : Fin (Fintype.card V) → ℝ) (k : Fin (Fintype.card V)),
      innerPi π (fun x => ∑ j, a j * ff j x) (ff k) = a k := by
    intro a k
    have e : ∀ x : V, (∑ j, a j * ff j x) * ff k x * π x
        = ∑ j, a j * (ff j x * ff k x * π x) := by
      intro x
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    show ∑ x : V, (∑ j, a j * ff j x) * ff k x * π x = a k
    rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_comm]
    have e2 : ∀ j, ∑ x : V, a j * (ff j x * ff k x * π x)
        = a j * (if j = k then 1 else 0) := by
      intro j
      rw [← Finset.mul_sum]
      exact congrArg _ (horth j k)
    rw [Finset.sum_congr rfl (fun j _ => e2 j),
      Finset.sum_eq_single_of_mem k (Finset.mem_univ k) (fun b _ hb => by simp [hb])]
    simp
  -- the constant function
  set one : V → ℝ := fun _ => 1 with hone_def
  have hPone : P.mulVec one = one := by
    funext x
    show ∑ y, P x y * 1 = 1
    simpa using hP.2 x
  have hone_eig : ∀ j, innerPi π one (ff j) * (lam j - 1) = 0 := by
    intro j
    have hA : P.mulVec one = fun x => ∑ k, (innerPi π one (ff k) * lam k) * ff k x := by
      funext x
      rw [mulVec_expand heig hpos hcomp one x]
    have hL : innerPi π (P.mulVec one) (ff j) = innerPi π one (ff j) * lam j := by
      rw [hA]; exact hcoef _ j
    rw [hPone] at hL
    linear_combination -hL
  have hc1 : ∃ j, innerPi π one (ff j) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ j, innerPi π one (ff j) * ff j (Classical.arbitrary V) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
    rw [expand hpos hcomp one (Classical.arbitrary V)] at h0
    exact one_ne_zero h0
  obtain ⟨j0, hj0⟩ := hc1
  have hlam0 : lam j0 = 1 := by
    rcases mul_eq_zero.mp (hone_eig j0) with h | h
    · exact absurd h hj0
    · linarith
  set x0 : V := Classical.arbitrary V with hx0_def
  have const_inner : ∀ u v : V → ℝ, (∀ x y : V, u x = u y) → (∀ x y : V, v x = v y) →
      innerPi π u v = u x0 * v x0 := by
    intro u v hu hv
    have e : ∀ x : V, u x * v x * π x = (u x0 * v x0) * π x := by
      intro x; rw [hu x x0, hv x x0]
    show ∑ x : V, u x * v x * π x = _
    rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum, hsum, mul_one]
  have hffconst : ∀ x y : V, ff j0 x = ff j0 y := by
    have h1 : P.mulVec (ff j0) = ff j0 := by
      rw [heig j0, hlam0, one_smul]
    exact (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j0) h1
  have ha : ff j0 x0 * ff j0 x0 = 1 := by
    have := horth j0 j0
    rw [const_inner _ _ hffconst hffconst] at this
    simpa using this
  have ha0 : ff j0 x0 ≠ 0 := by
    intro h; rw [h] at ha; norm_num at ha
  have hlamne : ∀ j, j ≠ j0 → lam j ≠ 1 := by
    intro j hj hlam1
    have h1 : P.mulVec (ff j) = ff j := by rw [heig j, hlam1, one_smul]
    have hcj : ∀ x y : V, ff j x = ff j y := (MarkovMixing.eigenvalue_basic P hP).2.1 hirr (ff j) h1
    have hb : ff j x0 * ff j0 x0 = 0 := by
      have := horth j j0
      rw [const_inner _ _ hcj hffconst] at this
      simpa [hj] using this
    have hbb : ff j x0 * ff j x0 = 1 := by
      have := horth j j
      rw [const_inner _ _ hcj hcj] at this
      simpa using this
    have : ff j x0 = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact h
      · exact absurd h ha0
    rw [this] at hbb
    norm_num at hbb
  -- the second-largest eigenvalue
  have hne : (Finset.univ.erase j0).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨jstar, hjs_mem, hjs⟩ := Finset.exists_max_image (Finset.univ.erase j0) lam hne
  have hjs_ne : jstar ≠ j0 := (Finset.mem_erase.mp hjs_mem).1
  have hffne : ∀ j, ff j ≠ 0 := by
    intro j h
    have := horth j j
    rw [h] at this
    simp [innerPi] at this
  have hgap : MarkovMixing.spectralGap P = 1 - lam jstar := by
    have hmem : lam jstar ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1} :=
      ⟨⟨ff jstar, hffne jstar, heig jstar⟩, hlamne jstar hjs_ne⟩
    have hbdd : ∀ r ∈ {l : ℝ | MarkovMixing.IsEigenvalue P l ∧ l ≠ 1}, r ≤ lam jstar := by
      rintro r ⟨⟨g, hg0, hg⟩, hr1⟩
      have hex : ∃ k, innerPi π g (ff k) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hg0
        funext x
        rw [← expand hpos hcomp g x]
        exact Finset.sum_eq_zero fun j _ => by rw [hcon j]; ring
      obtain ⟨k, hk⟩ := hex
      have hA : P.mulVec g = fun x => ∑ j, (innerPi π g (ff j) * lam j) * ff j x := by
        funext x
        rw [mulVec_expand heig hpos hcomp g x]
      have hL : innerPi π (P.mulVec g) (ff k) = innerPi π g (ff k) * lam k := by
        rw [hA]; exact hcoef _ k
      have hR : innerPi π (P.mulVec g) (ff k) = r * innerPi π g (ff k) := by
        rw [hg]
        show ∑ x : V, (r • g) x * ff k x * π x = r * ∑ x : V, g x * ff k x * π x
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by simp [Pi.smul_apply]; ring
      have hlamk : lam k = r := by
        have : innerPi π g (ff k) * lam k = innerPi π g (ff k) * r := by rw [← hL, hR]; ring
        exact mul_left_cancel₀ hk this
      have hkne : k ≠ j0 := by
        intro h; rw [h, hlam0] at hlamk; exact hr1 hlamk.symm
      rw [← hlamk]
      exact hjs k (Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩)
    show 1 - MarkovMixing.lambdaTwo P = 1 - lam jstar
    rw [show MarkovMixing.lambdaTwo P = lam jstar from
      le_antisymm (csSup_le ⟨_, hmem⟩ hbdd) (le_csSup ⟨lam jstar, hbdd⟩ hmem)]
  -- the minimiser
  have hfs_exp : MarkovMixing.distExp π (ff jstar) = 0 := by
    have h1 : innerPi π (ff jstar) (ff j0) = ff j0 x0 * MarkovMixing.distExp π (ff jstar) := by
      have e : ∀ x : V, ff jstar x * ff j0 x * π x = ff j0 x0 * (ff jstar x * π x) := by
        intro x; rw [hffconst x x0]; ring
      show ∑ x : V, ff jstar x * ff j0 x * π x = _
      rw [Finset.sum_congr rfl (fun x _ => e x), ← Finset.mul_sum]
      rfl
    rw [horth jstar j0] at h1
    simp [hjs_ne] at h1
    rcases h1 with h | h
    · exact absurd h ha0
    · exact h
  have hfs_norm : innerPi π (ff jstar) (ff jstar) = 1 := by simpa using horth jstar jstar
  have hfs_dir : MarkovMixing.dirichletForm P π (ff jstar) = 1 - lam jstar := by
    rw [hdir]
    rw [Finset.sum_eq_single_of_mem jstar (Finset.mem_univ jstar)
      (fun b _ hb => by rw [horth jstar b]; simp [Ne.symm hb])]
    rw [horth jstar jstar]
    simp
  have hmemS : (1 - lam jstar) ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f} :=
    ⟨ff jstar, hfs_exp, hfs_norm, hfs_dir.symm⟩
  have hlb : ∀ e ∈ {e : ℝ | ∃ f : V → ℝ, MarkovMixing.distExp π f = 0 ∧
      MarkovMixing.innerPi π f f = 1 ∧ e = MarkovMixing.dirichletForm P π f},
      1 - lam jstar ≤ e := by
    rintro e ⟨g, hgexp, hgnorm, rfl⟩
    have hc0 : innerPi π g (ff j0) = 0 := by
      have e1 : ∀ x : V, g x * ff j0 x * π x = ff j0 x0 * (g x * π x) := by
        intro x; rw [hffconst x x0]; ring
      have : innerPi π g (ff j0) = ff j0 x0 * MarkovMixing.distExp π g := by
        show ∑ x : V, g x * ff j0 x * π x = _
        rw [Finset.sum_congr rfl (fun x _ => e1 x), ← Finset.mul_sum]
        rfl
      rw [this, hgexp, mul_zero]
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Fintype.card V))),
        (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) ≤ (innerPi π g (ff j)) ^ 2 * (1 - lam j) := by
      intro j _
      by_cases hj : j = j0
      · subst hj; rw [hc0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have := hjs j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
        linarith
    calc 1 - lam jstar = (∑ j, (innerPi π g (ff j)) ^ 2) * (1 - lam jstar) := by
          rw [← norm_eq hpos hcomp g, hgnorm, one_mul]
      _ = ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam jstar) := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (innerPi π g (ff j)) ^ 2 * (1 - lam j) := Finset.sum_le_sum hterm
      _ = MarkovMixing.dirichletForm P π g := (hdir g).symm
  refine ⟨?_, ff jstar, hfs_exp, hfs_norm, ?_⟩
  · rw [hgap]
    exact le_antisymm (le_csInf ⟨_, hmemS⟩ hlb) (csInf_le ⟨1 - lam jstar, hlb⟩ hmemS)
  · rw [hgap, hfs_dir]

#print axioms MarkovMixing.dirichlet_gap

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing

theorem DiaconisStroock.Poincare.var_eq_half_sum_sq {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : IsDist π) (φ : V → ℝ) :
    distVar π φ = 2⁻¹ * ∑ x, ∑ y, (φ x - φ y)^2 * (π x * π y) := by
  let m := distExp π φ
  let S := ∑ x, φ x ^ 2 * π x
  have hm : (∑ x, φ x * π x) = m := rfl
  have hv : distVar π φ = S - m ^ 2 := by
    unfold distVar
    change (∑ x, (φ x - m)^2 * π x) = S - m^2
    have he : ∀ x, (φ x - m)^2 * π x =
        φ x^2 * π x - (2*m)*(φ x*π x) + m^2*π x := fun x => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hm, hπ.2]
    change S - 2*m*m + m^2*1 = S-m^2
    ring
  have hi : ∀ x, (∑ y, (φ x-φ y)^2*(π x*π y)) =
      φ x^2*π x - (2*m)*(φ x*π x) + S*π x := by
    intro x
    have he : ∀ y, (φ x-φ y)^2*(π x*π y) =
        (φ x^2*π x)*π y - (2*φ x*π x)*(φ y*π y) + (φ y^2*π y)*π x :=
      fun y => by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hπ.2, hm]
    change φ x^2*π x*1 - 2*φ x*π x*m + S*π x = _
    ring
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hm, hπ.2, hv]
  change S-m^2 = 2⁻¹*(S-2*m*m+S*1)
  norm_num
  ring
#print axioms DiaconisStroock.Poincare.var_eq_half_sum_sq

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare
namespace PoincarePath
lemma map_sum_eq {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  conv_lhs => rw [← List.ofFn_get l]
  rw [List.map_ofFn, List.sum_ofFn]
  rfl

lemma weighted {α : Type*} (l : List α) (w d : α → ℝ)
    (hw : ∀ a ∈ l, 0 < w a) :
    (l.map d).sum ^ 2 ≤ (l.map fun a => (w a)⁻¹).sum *
      (l.map fun a => w a * (d a)^2).sum := by
  simp_rw [map_sum_eq]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i _; exact le_of_lt (inv_pos.mpr (hw _ (List.get_mem _ _)))
  · intro i _; exact mul_nonneg (le_of_lt (hw _ (List.get_mem _ _))) (sq_nonneg _)
  · intro i _
    have hn : w (l.get i) ≠ 0 := ne_of_gt (hw _ (List.get_mem _ _))
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

lemma telescope {V : Type*} (φ : V → ℝ) (p : List V) (x y : V)
    (hx : p.head? = some x) (hy : p.getLast? = some y) :
    ((pathEdges p).map fun e => φ e.2 - φ e.1).sum = φ y - φ x := by
  induction p generalizing x with
  | nil => simp at hx
  | cons a p ih =>
    have ha : a = x := by simpa using hx
    subst x
    cases p with
    | nil =>
      have ha : a = y := by simpa using hy
      subst y
      simp [pathEdges]
    | cons b p =>
      have ht := ih b (by rfl) (by simpa only [List.getLast?_cons_cons] using hy)
      simpa only [pathEdges, List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.sum_cons] using (show (φ b - φ a) +
          ((pathEdges (b :: p)).map fun e => φ e.2 - φ e.1).sum = φ y - φ a by
            rw [ht]; ring)
end PoincarePath

theorem DiaconisStroock.Poincare.sq_sub_le_qLength_mul {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (x y : V) (p : List V) (hp : IsWalk P π x y p) (φ : V → ℝ) :
    (φ y - φ x)^2 ≤ qLength P π p *
      ((pathEdges p).map fun e => edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1)^2).sum := by
  have h := PoincarePath.weighted (pathEdges p)
    (fun e => edgeMeasure P π e.1 e.2) (fun e => φ e.2 - φ e.1) hp.2.2
  rw [PoincarePath.telescope φ p x y hp.1 hp.2.1] at h
  exact h
#print axioms DiaconisStroock.Poincare.sq_sub_le_qLength_mul

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare
namespace PoincareCongestion
lemma list_sum {α : Type*} [Fintype α] [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → ℝ) :
    (l.map f).sum = ∑ a, if a ∈ l then f a else 0 := by
  rw [← List.sum_toFinset f hl]
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp
end PoincareCongestion

theorem DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) (φ : V → ℝ) :
    distVar π φ ≤ kappa P π Γ * dirichletForm P π φ := by
  classical
  let E : V × V → ℝ := fun e => edgeMeasure P π e.1 e.2 * (φ e.2 - φ e.1)^2
  let C : V × V → ℝ := fun e => ∑ x, ∑ y,
    if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y) * π x * π y else 0
  have hE : ∀ e, 0 ≤ E e := fun e =>
    mul_nonneg (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2)) (sq_nonneg _)
  have hpair : ∀ x y, (φ x - φ y)^2 * (π x * π y) ≤
      ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
        then qLength P π (Γ x y) * π x * π y else 0) * E e := by
    intro x y
    by_cases hxy : x = y
    · subst y; simp
    · have hp := hΓ x y hxy
      have hn := List.Nodup.of_map Sym2.mk hp.2
      have hb := DiaconisStroock.Poincare.sq_sub_le_qLength_mul P hP π x y (Γ x y) hp.1 φ
      have hw := mul_le_mul_of_nonneg_right hb (mul_nonneg (hπ.1.1 x) (hπ.1.1 y))
      have hs := PoincareCongestion.list_sum (pathEdges (Γ x y)) hn E
      change ((pathEdges (Γ x y)).map E).sum = _ at hs
      rw [hs] at hw
      have heq : qLength P π (Γ x y) * (∑ e : V × V, if e ∈ pathEdges (Γ x y) then E e else 0) * (π x*π y) =
          ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
            then qLength P π (Γ x y)*π x*π y else 0)*E e := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e ∈ pathEdges (Γ x y) <;> simp [hxy, he] <;> ring
      calc
        (φ x-φ y)^2*(π x*π y) = (φ y-φ x)^2*(π x*π y) := by ring
        _ ≤ _ := hw
        _ = _ := by
          convert heq using 1
          congr 2
          apply Finset.sum_congr rfl
          intro e _
          split <;> simp_all
  have htotal : (∑ x, ∑ y, (φ x-φ y)^2*(π x*π y)) ≤ ∑ e : V × V, C e * E e := by
    calc
      _ ≤ ∑ x, ∑ y, ∑ e : V × V, (if x ≠ y ∧ e ∈ pathEdges (Γ x y)
          then qLength P π (Γ x y)*π x*π y else 0)*E e :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hpair x y
      _ = _ := by
        simp_rw [show ∀ x, (∑ y, ∑ e : V × V,
            (if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y)*π x*π y else 0)*E e) =
            ∑ e : V × V, ∑ y, (if x ≠ y ∧ e ∈ pathEdges (Γ x y) then qLength P π (Γ x y)*π x*π y else 0)*E e
            from fun x => Finset.sum_comm]
        rw [Finset.sum_comm]
        simp only [C, Finset.sum_mul]
  have hbound : ∀ e, C e * E e ≤ kappa P π Γ * E e := by
    intro e
    by_cases he : 0 < edgeMeasure P π e.1 e.2
    · have hc : C e ≤ kappa P π Γ :=
        le_ciSup (Finite.bddAbove_range
          (fun e : {e : V × V // 0 < edgeMeasure P π e.1 e.2} => C e.val)) ⟨e, he⟩
      exact mul_le_mul_of_nonneg_right hc (hE e)
    · have hz : edgeMeasure P π e.1 e.2 = 0 :=
        le_antisymm (le_of_not_gt he) (mul_nonneg (hπ.1.1 e.1) (hP.1 e.1 e.2))
      simp [E, hz]
  have henergy : (∑ e : V × V, E e) = 2 * dirichletForm P π φ := by
    rw [Fintype.sum_prod_type]
    unfold dirichletForm
    have ht : ∀ x y, E (x,y) = (φ x-φ y)^2*(π x*P x y) := by
      intro x y
      dsimp [E, edgeMeasure]
      ring
    simp_rw [ht]
    ring
  rw [DiaconisStroock.Poincare.var_eq_half_sum_sq π hπ.1 φ]
  have hb := htotal.trans (Finset.sum_le_sum fun e _ => hbound e)
  rw [← Finset.mul_sum, henergy] at hb
  nlinarith
#print axioms DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet

set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.Poincare

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hV : 2 ≤ Fintype.card V) (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / kappa P π Γ := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨f, hfmean, hfnorm, hfgap⟩ :=
    (MarkovMixing.dirichlet_gap hV P hP hirr π hπ hrev).2
  have hv : distVar π f = 1 := by
    calc
      distVar π f = ∑ x, (f x)^2 * π x := by simp [distVar, hfmean]
      _ = innerPi π f f := by simp only [innerPi, pow_two]
      _ = 1 := hfnorm
  have he : 0 ≤ dirichletForm P π f := by
    unfold dirichletForm
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    exact mul_nonneg (sq_nonneg _) (mul_nonneg (hπ.1.1 x) (hP.1 x y))
  have hb := DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet P hP hirr π hπ hrev Γ hΓ f
  rw [hv, ← hfgap] at hb
  have hg : 0 ≤ spectralGap P := by rwa [hfgap]
  have hk : 0 < kappa P π Γ := by
    by_contra hn
    have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hg
    linarith
  have hi : 1 / kappa P π Γ ≤ spectralGap P :=
    (div_le_iff₀ hk).mpr (by nlinarith [hb])
  unfold spectralGap at hi
  linarith
#print axioms solution

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- Proposition 1 (Poincaré inequality), p. 37, with κ defined by (1.5). -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hV : 2 ≤ Fintype.card V) (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / kappa P π Γ := by
  exact solution P hP hirr π hπ hrev hV Γ hΓ

end DiaconisStroock.Poincare

#print axioms solution
