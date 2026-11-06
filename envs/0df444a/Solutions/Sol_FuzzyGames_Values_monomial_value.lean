-- Prove2me | solution 1 for FuzzyGames.Values.monomial_value
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T03:25:41.508296+00:00
-- url     : https://prove2.me/submissions/868ecdd2-9348-4c21-b2fb-23d9ea7d4b8e

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

open FuzzyGames.Values

namespace FuzzyMonoAux

/-- A game invariant under all transpositions gets the equal split `v(τ^N)/M`. -/
lemma sym_value (ψ : (n : ℕ) → Vn n → (Fin n → ℝ))
    (hP : IsParetoOptimal ψ) (hS : IsSymmetric ψ) (M : ℕ) (hM : 0 < M) (b : Vn M)
    (hb : ∀ (i j : Fin M) (τ : Fin M → ℝ), b.1 τ = b.1 (fun k => τ (Equiv.swap i j k))) :
    ∀ j, ψ M b j = b.1 1 / M := by
  have heq : ∀ i j, ψ M b i = ψ M b j := by
    intro i j
    have := hS M hM (Equiv.swap i j) b b (fun τ => by
      rw [Equiv.symm_swap]; exact hb i j τ) i
    rw [this, Equiv.swap_apply_left]
  have hsum := hP M hM b
  intro j
  have : ∑ i, ψ M b i = M * ψ M b j := by
    rw [Finset.sum_congr rfl fun i _ => heq i j]; simp
  rw [this] at hsum
  field_simp
  linarith

/-- Transfer along a map `f : Fin M → Fin n` from a game with equal split. -/
lemma transfer (ψ : (n : ℕ) → Vn n → (Fin n → ℝ)) (hA : IsAtomic ψ)
    (M : ℕ) (hM : 2 ≤ M) (n : ℕ) (b : Vn M) (hb : ∀ j, ψ M b j = 1 / M)
    (f : Fin M → Fin n) (v : Vn n) (hv : ∀ σ : Fin n → ℝ, v.1 σ = b.1 (fun a => σ (f a)))
    (i : Fin n) :
    ψ n v i = ∑ a, if f a = i then (1 / M : ℝ) else 0 := by
  have hn : 0 < n := by
    have : 0 < M := by omega
    exact Fin.pos_iff_nonempty.2 ⟨f ⟨0, this⟩⟩
  -- the auxiliary game on `M + n` players
  let u : Vn (M + n) := ⟨fun x => b.1 (fun a => x (Fin.castAdd n a)), by
    refine ⟨b.2.1.comp (contDiff_pi.2 fun a => contDiff_apply ℝ ℝ _), ?_⟩
    exact b.2.2⟩
  have hu : ∀ x, u.1 x = b.1 (fun a => x (Fin.castAdd n a)) := fun x => rfl
  set c := ψ (M + n) u with hc
  have hsplit : ∀ (Q : Fin (M + n) → Fin M) (j : Fin M),
      ∑ x ∈ Finset.univ.filter (fun x => Q x = j), c x =
        ∑ a : Fin M, (if Q (Fin.castAdd n a) = j then c (Fin.castAdd n a) else 0) +
          ∑ i' : Fin n, (if Q (Fin.natAdd M i') = j then c (Fin.natAdd M i') else 0) := by
    intro Q j
    rw [Finset.sum_filter, Fin.sum_univ_add]
  -- merging the extra players into the types of `b`
  have hmerge : ∀ (g : Fin n → Fin M) (j : Fin M),
      1 / (M : ℝ) = c (Fin.castAdd n j) +
        ∑ i' : Fin n, (if g i' = j then c (Fin.natAdd M i') else 0) := by
    intro g j
    let Q : Fin (M + n) → Fin M := Fin.addCases (fun a => a) g
    have hQs : Function.Surjective Q := fun j => ⟨Fin.castAdd n j, by simp [Q]⟩
    have h := hA (M + n) (by omega) M Q hQs u b (fun σ => by
      rw [hu]; simp [Q]) j
    rw [hb j] at h
    rw [h, hsplit Q j]
    simp only [Q, Fin.addCases_left, Fin.addCases_right]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha; simp [ha]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have hnt : Nontrivial (Fin M) := Fin.nontrivial_iff_two_le.2 hM
  have hfirst : ∀ j : Fin M, c (Fin.castAdd n j) = 1 / M := by
    intro j
    obtain ⟨c0, hc0⟩ := exists_ne j
    have := hmerge (fun _ => c0) j
    beta_reduce at this
    simp only [hc0, if_false, Finset.sum_const_zero, add_zero] at this
    exact this.symm
  have hextra : ∀ i' : Fin n, c (Fin.natAdd M i') = 0 := by
    intro i'
    let j0 : Fin M := ⟨0, by omega⟩
    obtain ⟨c0, hc0⟩ := exists_ne j0
    have := hmerge (fun i'' => if i'' = i' then j0 else c0) j0
    rw [hfirst j0, Finset.sum_eq_single i'] at this
    · simp at this; linarith
    · intro b' _ hb'; simp [hb', hc0]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  -- the transfer to `v`
  let P : Fin (M + n) → Fin n := Fin.addCases f (fun i' => i')
  have hPs : Function.Surjective P := fun i => ⟨Fin.natAdd M i, by simp [P]⟩
  have h := hA (M + n) (by omega) n P hPs u v (fun σ => by
    rw [hv, hu]; simp [P]) i
  rw [h, Finset.sum_filter, Fin.sum_univ_add]
  simp only [P, Fin.addCases_left, Fin.addCases_right]
  have e1 : ∀ a, ψ (M + n) u (Fin.castAdd n a) = 1 / M := hfirst
  have e2 : ∀ i', ψ (M + n) u (Fin.natAdd M i') = 0 := hextra
  simp only [e1, e2, ite_self, Finset.sum_const_zero, add_zero]

lemma swap_prod {M : ℕ} (i j : Fin M) (τ : Fin M → ℝ) :
    ∏ k, τ k = ∏ k, τ (Equiv.swap i j k) :=
  (Equiv.prod_comp (Equiv.swap i j) τ).symm

lemma diag_monomial {n : ℕ} (k : Fin n → ℕ) (hk : k ≠ 0) (i : Fin n) :
    diagValue (monomial k) i = (k i : ℝ) / ((∑ j, k j : ℕ) : ℝ) := by
  set K := ∑ j, k j with hK
  have hKpos : 1 ≤ K := by
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    have : k j ≤ K := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hcd : ContDiff ℝ 1 (monomial k) := by
    unfold monomial
    exact contDiff_prod fun i _ => (contDiff_apply ℝ ℝ i).pow _
  have hdv : Differentiable ℝ (monomial k) := hcd.differentiable (by norm_num)
  have hrest : ∑ j ∈ Finset.univ.erase i, k j = K - k i := by
    rw [hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; omega
  have hint : ∀ t : ℝ, fderiv ℝ (monomial k) (t • (1 : Fin n → ℝ)) (Pi.single i 1) =
      (k i : ℝ) * t ^ (k i - 1) * t ^ (K - k i) := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => monomial k (t • (1 : Fin n → ℝ) + s • Pi.single i 1))
        (fderiv ℝ (monomial k) (t • (1 : Fin n → ℝ)) (Pi.single i 1)) 0 := by
      have hid : HasDerivAt (fun s : ℝ => t • (1 : Fin n → ℝ) + s • Pi.single i 1)
          (Pi.single i 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add
          (t • (1 : Fin n → ℝ))
      have hv : HasFDerivAt (monomial k) (fderiv ℝ (monomial k) (t • (1 : Fin n → ℝ)))
          (t • (1 : Fin n → ℝ) + (0 : ℝ) • Pi.single i 1) := by
        rw [zero_smul, add_zero]; exact (hdv _).hasFDerivAt
      exact HasFDerivAt.comp_hasDerivAt (l := monomial k)
        (f := fun s : ℝ => t • (1 : Fin n → ℝ) + s • Pi.single i 1) (0 : ℝ) hv hid
    have hform : (fun s : ℝ => monomial k (t • (1 : Fin n → ℝ) + s • Pi.single i 1)) =
        fun s => (t + s) ^ k i * t ^ (K - k i) := by
      funext s
      unfold monomial
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      congr 1
      · simp
      · rw [← hrest, ← Finset.prod_pow_eq_pow_sum]
        refine Finset.prod_congr rfl fun j hj => ?_
        have : j ≠ i := Finset.ne_of_mem_erase hj
        simp [Pi.single_apply, this]
    have h2 : HasDerivAt (fun s : ℝ => (t + s) ^ k i * t ^ (K - k i))
        ((k i : ℝ) * t ^ (k i - 1) * t ^ (K - k i)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_add t).pow (k i)).mul_const (t ^ (K - k i))
      simpa using this
    rw [hform] at h1
    exact h1.unique h2
  unfold diagValue
  simp_rw [hint]
  rcases Nat.eq_zero_or_pos (k i) with h0 | hpos
  · simp [h0]
  · have : ∀ t : ℝ, (k i : ℝ) * t ^ (k i - 1) * t ^ (K - k i) = (k i : ℝ) * t ^ (K - 1) := by
      intro t
      have hle : k i ≤ K := by
        rw [hK]; exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [mul_assoc, ← pow_add]; congr 2; omega
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hK1 : K - 1 + 1 = K := by omega
    have hc : ((K - 1 : ℕ) : ℝ) + 1 = K := by rw [← Nat.cast_succ, Nat.succ_eq_add_one, hK1]
    rw [hK1, hc, one_pow, zero_pow (by omega), sub_zero]
    ring

end FuzzyMonoAux

open FuzzyMonoAux in
theorem solution (ψ : (n : ℕ) → Vn n → (Fin n → ℝ))
    (hP : IsParetoOptimal ψ) (hS : IsSymmetric ψ) (hA : IsAtomic ψ) (n : ℕ)
    (k : Fin n → ℕ) (hk : k ≠ 0) (v : Vn n) (hv : ∀ τ : Fin n → ℝ, v.1 τ = monomial k τ)
    (i : Fin n) :
    ψ n v i = (k i : ℝ) / ((∑ j, k j : ℕ) : ℝ) ∧
      diagValue v.1 i = (k i : ℝ) / ((∑ j, k j : ℕ) : ℝ) := by
  have hvfun : v.1 = monomial k := funext hv
  refine ⟨?_, by rw [hvfun]; exact diag_monomial k hk i⟩
  set K := ∑ j, k j with hK
  have hKpos : 1 ≤ K := by
    obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    have : k j ≤ K := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  rcases Nat.lt_or_ge K 2 with hK1 | hK2
  · -- `K = 1`: `v = τ_s`; transfer from the two-player game `(σ₀ + σ₁)/2`
    have hK1' : K = 1 := by omega
    obtain ⟨s, hs⟩ : ∃ s, k s ≠ 0 := by
      by_contra h; push Not at h; exact hk (funext h)
    have hks : k s = 1 := by
      have : k s ≤ K := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ s)
      omega
    have hother : ∀ j, j ≠ s → k j = 0 := by
      intro j hj
      have h2 := Finset.add_sum_erase Finset.univ k (Finset.mem_univ s)
      have h3 : k j ≤ ∑ x ∈ Finset.univ.erase s, k x :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      rw [← hK] at h2; omega
    let b : Vn 2 := ⟨fun σ => (σ 0 + σ 1) / 2, by
      refine ⟨?_, by simp⟩
      exact ((contDiff_apply ℝ ℝ 0).add (contDiff_apply ℝ ℝ 1)).div_const 2⟩
    have hbsym := sym_value ψ hP hS 2 (by norm_num) b (by
      intro i j τ
      simp only [b]
      fin_cases i <;> fin_cases j <;> simp [Equiv.swap_apply_of_ne_of_ne] <;> ring)
    have hb : ∀ j, ψ 2 b j = 1 / (2 : ℕ) := by
      intro j; rw [hbsym j]; simp [b]
    have h := transfer ψ hA 2 le_rfl n b hb (fun _ => s) v (by
      intro σ; rw [hv]; simp only [b, monomial]
      rw [Finset.prod_eq_single s]
      · rw [hks]; ring
      · intro j _ hj; rw [hother j hj, pow_zero]
      · intro h'; exact absurd (Finset.mem_univ _) h') i
    rw [h, hK1']
    by_cases his : s = i
    · subst his; simp [hks]
    · have : k i = 0 := hother i (Ne.symm his)
      simp [his, this]
  · -- `K ≥ 2`: transfer from the product game on `K` players
    let e : (j : Fin n) × Fin (k j) ≃ Fin K := finSigmaFinEquiv
    let f : Fin K → Fin n := fun a => (e.symm a).1
    let b : Vn K := ⟨fun σ => ∏ a, σ a, by
      refine ⟨contDiff_prod fun a _ => contDiff_apply ℝ ℝ a, ?_⟩
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) rfl⟩
    have hbsym := sym_value ψ hP hS K (by omega) b (fun i j τ => swap_prod i j τ)
    have hb : ∀ j, ψ K b j = 1 / K := by
      intro j; rw [hbsym j]; simp [b]
    have h := transfer ψ hA K hK2 n b hb f v (by
      intro σ; rw [hv]; simp only [b, monomial, f]
      rw [← Equiv.prod_comp e (fun a => σ (e.symm a).1)]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.prod_sigma]
      simp) i
    rw [h]
    rw [← Equiv.sum_comp e (fun a => if f a = i then (1 / K : ℝ) else 0)]
    simp only [f, Equiv.symm_apply_apply]
    rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single i]
    · simp; ring
    · intro j _ hj; simp [hj]
    · intro h'; exact absurd (Finset.mem_univ _) h'
