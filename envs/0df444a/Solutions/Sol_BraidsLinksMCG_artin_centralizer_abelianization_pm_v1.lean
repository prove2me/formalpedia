-- Prove2me | solution 1 for BraidsLinksMCG.artin_centralizer_abelianization_pm_v1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:41:06.324957+00:00
-- url     : https://prove2.me/submissions/f8a56a65-0f9a-4ed9-9d5a-cb9a50f56963

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option autoImplicit false

namespace E7419006

open BraidsLinksMCG

/-- The abelianization coordinate vector of a word. -/
noncomputable def cnt (n : ℕ) : FreeGroup (Fin n) →* Multiplicative (Fin n → ℤ) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (Pi.single j 1)

noncomputable def v {n : ℕ} (w : FreeGroup (Fin n)) : Fin n → ℤ :=
  Multiplicative.toAdd (cnt n w)

lemma v_of {n : ℕ} (j : Fin n) : v (FreeGroup.of j) = Pi.single j 1 := by
  simp [v, cnt]

lemma v_mul {n : ℕ} (a b : FreeGroup (Fin n)) : v (a * b) = v a + v b := by
  simp [v, map_mul, toAdd_mul]

lemma v_inv {n : ℕ} (a : FreeGroup (Fin n)) : v a⁻¹ = - v a := by
  simp [v, map_inv, toAdd_inv]

lemma v_one {n : ℕ} : v (1 : FreeGroup (Fin n)) = 0 := by simp [v]

noncomputable def r {n : ℕ} (f : Fin n → ℤ) : Abelianization (FreeGroup (Fin n)) :=
  ∏ k, (Abelianization.of (FreeGroup.of k)) ^ (f k)

lemma r_add {n : ℕ} (f g : Fin n → ℤ) : r (f + g) = r f * r g := by
  simp [r, zpow_add, Finset.prod_mul_distrib]

lemma r_neg {n : ℕ} (f : Fin n → ℤ) : r (-f) = (r f)⁻¹ := by
  simp [r, zpow_neg, Finset.prod_inv_distrib]

lemma r_single {n : ℕ} (j : Fin n) :
    r (Pi.single j 1) = Abelianization.of (FreeGroup.of j) := by
  unfold r
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma r_v {n : ℕ} (w : FreeGroup (Fin n)) : r (v w) = Abelianization.of w := by
  induction w with
  | C1 => simp [v_one, r]
  | of x => rw [v_of, r_single]
  | inv_of x ih => rw [v_inv, r_neg, ih, map_inv]
  | mul x y hx hy => rw [v_mul, r_add, hx, hy, map_mul]

lemma inj {n : ℕ} (a b : FreeGroup (Fin n)) (h : v a = v b) :
    Abelianization.of a = Abelianization.of b := by
  rw [← r_v, ← r_v, h]

lemma v_hom {n : ℕ} {F : Type*} [FunLike F (FreeGroup (Fin n)) (FreeGroup (Fin n))]
    [MonoidHomClass F (FreeGroup (Fin n)) (FreeGroup (Fin n))] (φ : F)
    (w : FreeGroup (Fin n)) :
    v (φ w) = ∑ k, v w k • v (φ (FreeGroup.of k)) := by
  induction w with
  | C1 => simp [v_one]
  | of x => simp [v_of, Pi.single_apply]
  | inv_of x ih => rw [map_inv, v_inv, ih, v_inv]; simp [Finset.sum_neg_distrib, neg_smul]
  | mul x y hx hy =>
    rw [map_mul, v_mul, hx, hy, v_mul]; simp [add_smul, Finset.sum_add_distrib]

lemma single_perm {n : ℕ} (j : Fin n) (σ : Equiv.Perm (Fin n)) (m : Fin n) :
    (Pi.single j (1 : ℤ) : Fin n → ℤ) (σ m) = (Pi.single (σ.symm j) (1 : ℤ) : Fin n → ℤ) m := by
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

lemma v_artin_of {n : ℕ} (i : Fin (n - 1)) (x : Fin n) :
    v (artinEndo n i (FreeGroup.of x)) =
      Pi.single (Equiv.swap (strandIdx i) (strandIdxSucc i) x) 1 := by
  have hne : strandIdx i ≠ strandIdxSucc i := by
    simp [strandIdx, strandIdxSucc, Fin.ext_iff]
  simp only [artinEndo, FreeGroup.lift_apply_of]
  split_ifs with h1 h2
  · subst h1
    rw [Equiv.swap_apply_left, v_mul, v_mul, v_inv, v_of, v_of]
    abel
  · subst h2
    rw [Equiv.swap_apply_right, v_of]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, v_of]

lemma v_artin {n : ℕ} (i : Fin (n - 1)) (w : FreeGroup (Fin n)) :
    v (artinEndo n i w) = fun m => v w (Equiv.swap (strandIdx i) (strandIdxSucc i) m) := by
  induction w with
  | C1 => funext m; simp [v_one]
  | of x =>
    funext m
    rw [v_artin_of, v_of, single_perm, Equiv.symm_swap]
  | inv_of x ih =>
    rw [map_inv, v_inv, ih, v_inv]; rfl
  | mul x y hx hy =>
    rw [map_mul, v_mul, hx, hy, v_mul]; rfl

lemma perm_inv {k : ℕ} (M : Fin (k + 1) → Fin (k + 1) → ℤ)
    (h : ∀ i : Fin k, ∀ j m, M (Equiv.swap i.castSucc i.succ j)
      (Equiv.swap i.castSucc i.succ m) = M j m)
    (σ : Equiv.Perm (Fin (k + 1))) : ∀ j m, M (σ j) (σ m) = M j m := by
  let S : Submonoid (Equiv.Perm (Fin (k + 1))) :=
    { carrier := {σ | ∀ j m, M (σ j) (σ m) = M j m}
      one_mem' := by intro j m; rfl
      mul_mem' := by
        intro a b ha hb j m
        have ha' : ∀ j m, M (a j) (a m) = M j m := ha
        have hb' : ∀ j m, M (b j) (b m) = M j m := hb
        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
        rw [ha', hb'] }
  have hS : Submonoid.closure (Set.range fun i : Fin k ↦ Equiv.swap i.castSucc i.succ) ≤ S := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h i
  have : σ ∈ S := hS (by rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial)
  exact this

lemma shape {n : ℕ} (M : Fin n → Fin n → ℤ)
    (hP : ∀ σ : Equiv.Perm (Fin n), ∀ j m, M (σ j) (σ m) = M j m)
    (a b : Fin n) (hab : a ≠ b) :
    ∀ j m, M j m = if j = m then M a a else M a b := by
  intro j m
  split_ifs with hjm
  · subst hjm
    have := hP (Equiv.swap a j) a a
    rw [Equiv.swap_apply_left] at this
    exact this
  · have h1 := hP (Equiv.swap a j) a (Equiv.swap a j m)
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self] at h1
    have hm'a : Equiv.swap a j m ≠ a := by
      intro h
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
      exact hjm h.symm
    have h2 := hP (Equiv.swap b (Equiv.swap a j m)) a (Equiv.swap a j m)
    rw [Equiv.swap_apply_of_ne_of_ne hab (Ne.symm hm'a), Equiv.swap_apply_right] at h2
    rw [h1, h2]

lemma form {n : ℕ} (hn : 3 ≤ n) (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w)) :
    ∃ d g : ℤ, ∀ j m : Fin n, v (beta (FreeGroup.of j)) m = if j = m then d else g := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  let M : Fin (k + 1) → Fin (k + 1) → ℤ := fun j m => v (beta (FreeGroup.of j)) m
  have hadj : ∀ i : Fin k, ∀ j m, M (Equiv.swap i.castSucc i.succ j)
      (Equiv.swap i.castSucc i.succ m) = M j m := by
    intro i j m
    have hs : strandIdx (n := k + 1) i = i.castSucc := Fin.ext rfl
    have hs' : strandIdxSucc (n := k + 1) i = i.succ := Fin.ext rfl
    have h := congrArg v (hcentral i (FreeGroup.of j))
    rw [v_hom beta, v_artin_of, v_artin] at h
    rw [hs, hs'] at h
    have h2 := congrFun h (Equiv.swap i.castSucc i.succ m)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.swap_apply_self] at h2
    rw [Finset.sum_eq_single (Equiv.swap i.castSucc i.succ j)] at h2
    · simpa [M] using h2
    · intro b _ hb; simp [hb]
    · simp
  have hP := perm_inv M hadj
  have hab : (⟨0, by omega⟩ : Fin (k + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact ⟨_, _, shape M hP _ _ hab⟩

lemma sum_form {n : ℕ} (d g d' g' : ℤ) (j m : Fin n) :
    ∑ k : Fin n, (if j = k then d else g) * (if k = m then d' else g') =
      (if j = m then (d - g) * (d' - g') else 0) + (d - g) * g' + g * (d' - g') +
        n * g * g' := by
  have e1 : ∀ k, (if j = k then d else g) = g + if j = k then d - g else 0 := by
    intro k; split_ifs <;> ring
  have e2 : ∀ k, (if k = m then d' else g') = g' + if k = m then d' - g' else 0 := by
    intro k; split_ifs <;> ring
  simp_rw [e1, e2, add_mul, mul_add, Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul, mul_ite]
  split_ifs <;> ring

lemma arith (n a a' g g' : ℤ) (hn : 3 ≤ n) (h1 : a * a' = 1)
    (h2 : a * g' + g * a' + n * g * g' = 0) : g = 0 ∧ (a = 1 ∨ a = -1) := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have h3 : (n * g + 1) * (n * g' + 1) = 1 := by linear_combination n * h2
    refine ⟨?_, Or.inl rfl⟩
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h3 with h | h
    · have : n * g = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · exact h'
    · exfalso
      rcases lt_trichotomy g 0 with hg | hg | hg
      · nlinarith
      · subst hg; simp at h
      · nlinarith
  · have h3 : (n * g - 1) * (n * g' - 1) = 1 := by linear_combination n * h2
    refine ⟨?_, Or.inr rfl⟩
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h3 with h | h
    · exfalso
      rcases lt_trichotomy g 0 with hg | hg | hg
      · nlinarith
      · subst hg; simp at h
      · nlinarith
    · have : n * g = 0 := by linarith
      rcases mul_eq_zero.1 this with h' | h'
      · omega
      · exact h'

end E7419006

open BraidsLinksMCG in
theorem solution
    (n : ℕ) (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w)) :
    (∀ j : Fin n, Abelianization.of (beta (FreeGroup.of j)) =
      Abelianization.of (FreeGroup.of j)) ∨
    (∀ j : Fin n, Abelianization.of (beta (FreeGroup.of j)) =
      Abelianization.of ((FreeGroup.of j)⁻¹)) := by
  have hsymm : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta.symm (artinEndo n i w) = artinEndo n i (beta.symm w) := by
    intro i w
    apply beta.injective
    rw [MulEquiv.apply_symm_apply, hcentral, MulEquiv.apply_symm_apply]
  obtain ⟨d, g, hM⟩ := E7419006.form hn beta hcentral
  obtain ⟨d', g', hM'⟩ := E7419006.form hn beta.symm hsymm
  have key : ∀ j m : Fin n, (Pi.single j (1 : ℤ) : Fin n → ℤ) m =
      ∑ k, (if j = k then d else g) * (if k = m then d' else g') := by
    intro j m
    have hc := E7419006.v_hom beta.symm (beta (FreeGroup.of j))
    rw [MulEquiv.symm_apply_apply, E7419006.v_of] at hc
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hM, hM']
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hne : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h00 := key i0 i0
  have h01 := key i0 i1
  rw [E7419006.sum_form] at h00 h01
  simp only [Pi.single_eq_same, if_true, Pi.single_eq_of_ne' hne, if_neg hne] at h00 h01
  have hn' : (3 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  obtain ⟨hg, hd⟩ := E7419006.arith (n : ℤ) (d - g) (d' - g') g g' hn'
    (by linarith) (by linarith)
  subst hg
  simp only [sub_zero] at hd
  rcases hd with rfl | rfl
  · left
    intro j
    apply E7419006.inj
    funext m
    rw [hM, E7419006.v_of, Pi.single_apply]
    by_cases h : j = m
    · subst h; simp
    · simp [h, Ne.symm h]
  · right
    intro j
    apply E7419006.inj
    funext m
    rw [hM, E7419006.v_inv, E7419006.v_of, Pi.neg_apply, Pi.single_apply]
    by_cases h : j = m
    · subst h; simp
    · simp [h, Ne.symm h]
