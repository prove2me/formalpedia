-- Prove2me | solution 1 for BB6Kit.prop37_order
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:52:27.351449+00:00
-- url     : https://prove2.me/submissions/094db067-fe96-4c73-bb57-050062492627

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta

open Finset

namespace PO

lemma diff_iter (h : ℂ → ℂ) (hh : Differentiable ℂ h) : ∀ k : ℕ, Differentiable ℂ (iteratedDeriv k h)
  | 0 => by rw [iteratedDeriv_zero]; exact hh
  | k + 1 => by
      rw [iteratedDeriv_succ]
      exact differentiableOn_univ.mp
        ((differentiableOn_univ.mpr (diff_iter h hh k)).deriv isOpen_univ)

lemma iter_mul_z (h : ℂ → ℂ) (hh : Differentiable ℂ h) : ∀ n : ℕ,
    iteratedDeriv (n + 1) (fun z => z * h z) =
      fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z := by
  have hd : ∀ (k : ℕ) (z : ℂ), HasDerivAt (iteratedDeriv k h) (iteratedDeriv (k + 1) h z) z := by
    intro k z
    rw [iteratedDeriv_succ]
    exact (diff_iter h hh k z).hasDerivAt
  intro n
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext z
    have h1 : HasDerivAt (fun z => z * h z) (1 * h z + z * deriv h z) z :=
      (hasDerivAt_id z).mul (hh z).hasDerivAt
    rw [h1.deriv, iteratedDeriv_zero, iteratedDeriv_one]
    push_cast
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have h1 : HasDerivAt (fun z => ((n : ℂ) + 1) * iteratedDeriv n h z + z * iteratedDeriv (n + 1) h z)
        (((n : ℂ) + 1) * iteratedDeriv (n + 1) h z + (1 * iteratedDeriv (n + 1) h z + z * iteratedDeriv (n + 1 + 1) h z)) z :=
      ((hd n z).const_mul _).add ((hasDerivAt_id z).mul (hd (n + 1) z))
    rw [h1.deriv]
    push_cast
    ring

lemma factor : ∀ J : ℕ, ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ n < J, iteratedDeriv n f 0 = 0) →
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = z ^ J * g z := by
  intro J
  induction J with
  | zero =>
    intro f hf _
    exact ⟨f, hf, fun z => by simp⟩
  | succ J ih =>
    intro f hf hJ
    have hf0 : f 0 = 0 := by
      have := hJ 0 (Nat.succ_pos _)
      rwa [iteratedDeriv_zero] at this
    have hdh : Differentiable ℂ (dslope f 0) :=
      differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
    have hfz : ∀ z, f z = z * dslope f 0 z := by
      intro z
      have := sub_smul_dslope f 0 z
      rw [smul_eq_mul, sub_zero, hf0, sub_zero] at this
      exact this.symm
    have hfeq : f = fun z => z * dslope f 0 z := funext hfz
    have hvan : ∀ n < J, iteratedDeriv n (dslope f 0) 0 = 0 := by
      intro n hn
      have h1 := hJ (n + 1) (by omega)
      rw [hfeq, iter_mul_z _ hdh n] at h1
      simp only [zero_mul, add_zero] at h1
      have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      exact (mul_eq_zero.mp h1).resolve_left hn1
    obtain ⟨g, hg, hgz⟩ := ih (dslope f 0) hdh hvan
    refine ⟨g, hg, fun z => ?_⟩
    rw [hfz z, hgz z]
    ring

lemma pow_mul_vanish : ∀ J : ℕ, ∀ G : ℂ → ℂ, Differentiable ℂ G →
    ∀ n < J, iteratedDeriv n (fun x => x ^ J * G x) 0 = 0 := by
  intro J
  induction J with
  | zero => intro G _ n hn; omega
  | succ J ih =>
    intro G hG n hn
    have hH : Differentiable ℂ (fun x => x ^ J * G x) := (differentiable_pow J).mul hG
    have e : (fun x : ℂ => x ^ (J + 1) * G x) = fun x => x * (x ^ J * G x) := by
      funext x; ring
    rw [e]
    cases n with
    | zero => simp
    | succ n' =>
      rw [iter_mul_z _ hH n']
      simp only [zero_mul, add_zero]
      rw [ih G hG n' (by omega), mul_zero]

lemma expsum_iter {ι : Type*} (s : Finset ι) (a b : ι → ℂ) : ∀ t : ℕ,
    iteratedDeriv t (fun x => ∑ σ ∈ s, a σ * Complex.exp (x * b σ)) =
      fun x => ∑ σ ∈ s, a σ * b σ ^ t * Complex.exp (x * b σ) := by
  intro t
  induction t with
  | zero => funext x; simp
  | succ t ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hsum := HasDerivAt.sum (u := s) (A := fun σ y => a σ * b σ ^ t * Complex.exp (y * b σ))
      (A' := fun σ => a σ * b σ ^ t * (Complex.exp (x * b σ) * b σ)) (x := x)
      (fun σ _ => ((hasDerivAt_mul_const (b σ)).cexp).const_mul (a σ * b σ ^ t))
    have h2 : (∑ σ ∈ s, fun y => a σ * b σ ^ t * Complex.exp (y * b σ)) =
        fun y => ∑ σ ∈ s, a σ * b σ ^ t * Complex.exp (y * b σ) := by
      funext y
      rw [Finset.sum_apply]
    rw [h2] at hsum
    rw [hsum.deriv]
    apply sum_congr rfl
    intro σ _
    ring

lemma det_rows_sum {N : ℕ} (S : Fin N → Finset ℕ) (a : Fin N → ℕ → ℂ) (v : Fin N → ℕ → Fin N → ℂ) :
    (Matrix.of fun i j => ∑ r ∈ S i, a i r * v i r j).det =
      ∑ f ∈ Fintype.piFinset S, (∏ i, a i (f i)) * (Matrix.of fun i j => v i (f i) j).det := by
  have h : ∀ M : Matrix (Fin N) (Fin N) ℂ,
      M.det = ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M i (σ i) := by
    intro M
    rw [← Matrix.det_transpose, Matrix.det_apply]
    apply sum_congr rfl
    intro σ _
    rw [Units.smul_def, zsmul_eq_mul]
    rfl
  rw [h]
  simp only [Matrix.of_apply, prod_univ_sum, mul_sum]
  simp_rw [h]
  simp only [Matrix.of_apply, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro f _
  apply sum_congr rfl
  intro σ _
  rw [prod_mul_distrib]
  ring

lemma prod_fiber {t N : ℕ} (g : Fin t → Fin N) (h : Fin N → ℂ) :
    ∏ s, h (g s) = ∏ i, h i ^ (univ.filter (fun s => g s = i)).card := by
  rw [← prod_fiberwise univ g (fun s => h (g s))]
  apply prod_congr rfl
  intro i _
  rw [prod_congr rfl (fun s hs => by rw [(mem_filter.mp hs).2]), prod_const]

lemma mem_rowSet {K L : ℕ} (p : ℕ × ℕ × ℕ) :
    p ∈ BB6Kit.rowSet K L ↔ p.1 < K ∧ p.2.1 < K ∧ p.2.2 < L ∧ p.1 + p.2.1 ≤ K - 1 := by
  unfold BB6Kit.rowSet
  simp only [mem_filter, mem_product, mem_range]
  tauto

/-- The alternation step (Waldschmidt, Lemma 7.2): rows of `I` are combinations of monomials
`w^α ζ^β` with `β ≤ K - 1`; too small a total degree forces two equal monomial rows. -/
lemma alt {N K L : ℕ} (I : Finset (Fin N)) (kml : Fin N → ℕ × ℕ × ℕ) (hmem : ∀ i, kml i ∈ BB6Kit.rowSet K L)
    (n : Fin N → ℕ) (a1 a2 : ℂ) (ha1 : a1 ≠ 0) (lead : Fin N → ℂ) (coef : Fin N → Fin N → ℂ)
    (hcoef : ∀ i ∈ I, ∀ j, coef i j = 1) (w ζ η : Fin N → ℂ) (hw : ∀ j, w j = η j * a1 + ζ j * a2)
    (hsmall : ∑ i, ((kml i).1 + (kml i).2.1 + n i) < BB6Theta.theta (K - 1) I.card) :
    (Matrix.of fun i j => coef i j * lead i * η j ^ (kml i).1 * ζ j ^ (kml i).2.1 * w j ^ (n i)).det = 0 := by
  obtain ⟨S, hS⟩ : ∃ S : Fin N → Finset ℕ, S = fun i => if i ∈ I then range ((kml i).1 + 1) else {0} := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Fin N → ℕ → ℂ, A = fun i r => if i ∈ I then
      lead i * a1⁻¹ ^ (kml i).1 * (-a2) ^ ((kml i).1 - r) * ((kml i).1.choose r : ℂ) else 1 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin N → ℕ → Fin N → ℂ, V = fun i r j => if i ∈ I then
      w j ^ (r + n i) * ζ j ^ ((kml i).1 - r + (kml i).2.1) else
      coef i j * lead i * η j ^ (kml i).1 * ζ j ^ (kml i).2.1 * w j ^ (n i) := ⟨_, rfl⟩
  have hM : (Matrix.of fun i j => coef i j * lead i * η j ^ (kml i).1 * ζ j ^ (kml i).2.1 * w j ^ (n i)) =
      Matrix.of fun i j => ∑ r ∈ S i, A i r * V i r j := by
    ext i j
    simp only [Matrix.of_apply]
    by_cases hi : i ∈ I
    · rw [hS, hA, hV]
      simp only [if_pos hi]
      rw [hcoef i hi j, one_mul]
      have hη : η j = (w j + -a2 * ζ j) * a1⁻¹ := by
        rw [hw j]
        field_simp
        ring
      have hpow : ((w j + -a2 * ζ j) * a1⁻¹) ^ (kml i).1 =
          a1⁻¹ ^ (kml i).1 * ∑ r ∈ range ((kml i).1 + 1), w j ^ r * (-a2 * ζ j) ^ ((kml i).1 - r) *
            ((kml i).1.choose r : ℂ) := by
        rw [mul_pow, add_pow, mul_comm]
      rw [hη, hpow]
      simp only [mul_sum, sum_mul]
      apply sum_congr rfl
      intro r hr
      rw [mem_range] at hr
      have e1 : w j ^ (r + n i) = w j ^ r * w j ^ (n i) := pow_add _ _ _
      have e2 : ζ j ^ ((kml i).1 - r + (kml i).2.1) = ζ j ^ ((kml i).1 - r) * ζ j ^ (kml i).2.1 := pow_add _ _ _
      rw [e1, e2, mul_pow]
      ring
    · rw [hS, hA, hV]
      simp [if_neg hi]
  rw [hM, det_rows_sum]
  apply sum_eq_zero
  intro f hf
  rw [Fintype.mem_piFinset] at hf
  have hfle : ∀ i ∈ I, f i ≤ (kml i).1 := by
    intro i hi
    have := hf i
    rw [hS] at this
    simp only [if_pos hi, mem_range] at this
    omega
  by_cases hinj : Set.InjOn (fun i => (f i + n i, (kml i).1 - f i + (kml i).2.1)) (I : Set (Fin N))
  · exfalso
    have hcard : (I.image (fun i => (f i + n i, (kml i).1 - f i + (kml i).2.1))).card = I.card :=
      card_image_of_injOn hinj
    have hbound : ∀ p ∈ I.image (fun i => (f i + n i, (kml i).1 - f i + (kml i).2.1)), p.2 ≤ K - 1 := by
      intro p hp
      rw [mem_image] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      have := (mem_rowSet (kml i)).mp (hmem i)
      dsimp only
      omega
    have hth : BB6Theta.theta (K - 1) I.card ≤
        ∑ p ∈ I.image (fun i => (f i + n i, (kml i).1 - f i + (kml i).2.1)), (p.1 + p.2) :=
      Nat.sInf_le ⟨_, hcard, hbound, rfl⟩
    have hsum : ∑ p ∈ I.image (fun i => (f i + n i, (kml i).1 - f i + (kml i).2.1)), (p.1 + p.2) =
        ∑ i ∈ I, ((kml i).1 + (kml i).2.1 + n i) := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro i hi
      have := hfle i hi
      dsimp only
      omega
    have hsub : ∑ i ∈ I, ((kml i).1 + (kml i).2.1 + n i) ≤ ∑ i, ((kml i).1 + (kml i).2.1 + n i) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun _ _ _ => Nat.zero_le _)
    omega
  · rw [Set.InjOn] at hinj
    push_neg at hinj
    obtain ⟨i1, hi1, i2, hi2, heq, hne⟩ := hinj
    simp only [Prod.mk.injEq] at heq
    rw [mul_eq_zero]
    right
    apply Matrix.det_zero_of_row_eq hne
    funext j
    rw [hV]
    simp only [Matrix.of_apply, if_pos (show i1 ∈ I from hi1), if_pos (show i2 ∈ I from hi2)]
    rw [heq.1, heq.2]

lemma ent (c lead x e z l a b : ℂ) (k m : ℕ) :
    c * (lead * (x * e) ^ k * (x * z) ^ m * Complex.exp (l * (x * e * a + x * z * b))) =
      x ^ (k + m) * (c * lead * e ^ k * z ^ m) * Complex.exp (x * (l * (e * a + z * b))) := by
  rw [show l * (x * e * a + x * z * b) = x * (l * (e * a + z * b)) by ring]
  ring

end PO

theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst) :
    ∀ I : Finset (Fin N), Differentiable ℂ (fun x => BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x) ∧
      ∀ n < BB6Theta.theta (K - 1) I.card, iteratedDeriv n (fun x => BB6Psi.psi N L R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3) b3 α1 α2 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) kml rst I x) 0 = 0 := by
  intro I
  generalize b1 / Nat.gcd b1 b3 = c1
  generalize b3 / Nat.gcd b1 b3 = c2
  generalize b2 / Nat.gcd b2 b3 = c3
  generalize b3 / Nat.gcd b2 b3 = c4
  generalize ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) = Λ at hΛ ⊢
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℂ, a1 = ((Real.log (α1 : ℝ) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℂ, a2 = ((Real.log (α2 : ℝ) : ℝ) : ℂ) := ⟨_, rfl⟩
  have ha1ne : a1 ≠ 0 := by
    rw [ha1]
    have : 0 < Real.log (α1 : ℝ) := Real.log_pos (by exact_mod_cast hα1)
    exact_mod_cast this.ne'
  obtain ⟨η, hη⟩ : ∃ η : Fin N → ℂ, η = fun j => ((BB6Psi.eta R T c1 c2 (rst j) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin N → ℂ, ζ = fun j => ((BB6Psi.zeta S T c3 c4 (rst j) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin N → ℂ, w = fun j => η j * a1 + ζ j * a2 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin N → ℂ, lam = fun i => ((BB6Psi.lam L (kml i) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨coef, hcoef⟩ : ∃ coef : Fin N → Fin N → ℂ, coef = fun i j =>
      if i ∈ I then (1 : ℂ) else ((BB6Psi.theta L T b3 Λ (kml i) (rst j) : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨lead, hlead⟩ : ∃ lead : Fin N → ℂ, lead = fun i => (c2 : ℂ) ^ (kml i).1 * (c4 : ℂ) ^ (kml i).2.1 /
      (((kml i).1.factorial : ℂ) * ((kml i).2.1.factorial : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs : Equiv.Perm (Fin N) → ℂ, Cs = fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∏ i, (coef i (σ i) * lead i * η (σ i) ^ (kml i).1 * ζ (σ i) ^ (kml i).2.1) := ⟨_, rfl⟩
  obtain ⟨Ss, hSs⟩ : ∃ Ss : Equiv.Perm (Fin N) → ℂ, Ss = fun σ => ∑ i, lam i * w (σ i) := ⟨_, rfl⟩
  -- Step 1: Ψ(x) = x^D · Σ_σ C_σ e^{x S_σ}
  have hΨ : (fun x => BB6Psi.psi N L R S T c1 c2 c3 c4 b3 α1 α2 Λ kml rst I x) = fun x => x ^ (∑ i, ((kml i).1 + (kml i).2.1)) *
      ∑ σ : Equiv.Perm (Fin N), Cs σ * Complex.exp (x * Ss σ) := by
    funext x
    unfold BB6Psi.psi
    rw [← Matrix.det_transpose, Matrix.det_apply, mul_sum]
    apply sum_congr rfl
    intro σ _
    rw [Units.smul_def, zsmul_eq_mul]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    have hent : ∀ i, (if i ∈ I then (1 : ℂ) else ((BB6Psi.theta L T b3 Λ (kml i) (rst (σ i)) : ℝ) : ℂ)) *
        BB6Psi.phi c2 c4 α1 α2 L (kml i) (x * ((BB6Psi.eta R T c1 c2 (rst (σ i)) : ℝ) : ℂ))
          (x * ((BB6Psi.zeta S T c3 c4 (rst (σ i)) : ℝ) : ℂ)) =
        x ^ ((kml i).1 + (kml i).2.1) * (coef i (σ i) * lead i * η (σ i) ^ (kml i).1 * ζ (σ i) ^ (kml i).2.1) *
          Complex.exp (x * (lam i * w (σ i))) := by
      intro i
      rw [hcoef, hlead, hw, hη, hζ, hlam, ha1, ha2]
      beta_reduce
      unfold BB6Psi.phi
      exact PO.ent _ _ _ _ _ _ _ _ _ _
    rw [prod_congr rfl (fun i _ => hent i), prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum,
      ← Complex.exp_sum, ← mul_sum, hCs, hSs]
    ring
  -- Step 2: derivatives of the exponential sum
  have hFdiff : Differentiable ℂ (fun x => ∑ σ : Equiv.Perm (Fin N), Cs σ * Complex.exp (x * Ss σ)) := by
    fun_prop
  have hFder : ∀ t, iteratedDeriv t (fun x => ∑ σ : Equiv.Perm (Fin N), Cs σ * Complex.exp (x * Ss σ)) 0 =
      ∑ σ : Equiv.Perm (Fin N), Cs σ * Ss σ ^ t := by
    intro t
    rw [PO.expsum_iter univ Cs Ss t]
    simp
  -- Step 3: the alternation
  have halt : ∀ t, (∑ i, ((kml i).1 + (kml i).2.1)) + t < BB6Theta.theta (K - 1) I.card →
      ∑ σ : Equiv.Perm (Fin N), Cs σ * Ss σ ^ t = 0 := by
    intro t ht
    have hexpand : ∀ σ : Equiv.Perm (Fin N), Ss σ ^ t =
        ∑ g ∈ Fintype.piFinset (fun _ : Fin t => (univ : Finset (Fin N))), ∏ s, lam (g s) * w (σ (g s)) := by
      intro σ
      rw [hSs]
      beta_reduce
      rw [← Fin.prod_const, prod_univ_sum]
    simp_rw [hexpand, mul_sum]
    rw [sum_comm]
    apply sum_eq_zero
    intro g _
    have hfib : ∀ σ : Equiv.Perm (Fin N), ∏ s, lam (g s) * w (σ (g s)) =
        (∏ i, lam i ^ (univ.filter (fun s => g s = i)).card) *
          ∏ i, w (σ i) ^ (univ.filter (fun s => g s = i)).card := by
      intro σ
      have := PO.prod_fiber g (fun i => lam i * w (σ i))
      beta_reduce at this
      rw [this]
      simp only [mul_pow, prod_mul_distrib]
    have hdet : ∑ σ : Equiv.Perm (Fin N), Cs σ * ∏ i, w (σ i) ^ (univ.filter (fun s => g s = i)).card =
        (Matrix.of fun i j => coef i j * lead i * η j ^ (kml i).1 * ζ j ^ (kml i).2.1 *
          w j ^ (univ.filter (fun s => g s = i)).card).det := by
      rw [← Matrix.det_transpose, Matrix.det_apply]
      apply sum_congr rfl
      intro σ _
      rw [Units.smul_def, zsmul_eq_mul, hCs]
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      rw [mul_assoc, ← prod_mul_distrib]
    have hzero := PO.alt I kml hrows.2 (fun i => (univ.filter (fun s => g s = i)).card) a1 a2 ha1ne lead coef
      (by intro i hi j; rw [hcoef]; simp [hi]) w ζ η (by intro j; rw [hw])
      (by
        have hc : ∑ i, (univ.filter (fun s => g s = i)).card = t := by
          rw [← card_eq_sum_card_fiberwise (fun s _ => mem_univ (g s)), card_univ, Fintype.card_fin]
        rw [sum_add_distrib, hc]
        exact ht)
    beta_reduce at hzero
    calc ∑ σ : Equiv.Perm (Fin N), Cs σ * ∏ s, lam (g s) * w (σ (g s))
        = (∏ i, lam i ^ (univ.filter (fun s => g s = i)).card) *
            ∑ σ : Equiv.Perm (Fin N), Cs σ * ∏ i, w (σ i) ^ (univ.filter (fun s => g s = i)).card := by
          rw [mul_sum]
          apply sum_congr rfl
          intro σ _
          rw [hfib σ]
          ring
      _ = 0 := by rw [hdet, hzero, mul_zero]
  -- Step 4: factor and conclude
  obtain ⟨G, hG, hGz⟩ := PO.factor (BB6Theta.theta (K - 1) I.card - ∑ i, ((kml i).1 + (kml i).2.1))
    _ hFdiff (fun t ht => by rw [hFder]; exact halt t (by omega))
  have hΨ2 : (fun x => BB6Psi.psi N L R S T c1 c2 c3 c4 b3 α1 α2 Λ kml rst I x) = fun x => x ^ ((∑ i, ((kml i).1 + (kml i).2.1)) +
      (BB6Theta.theta (K - 1) I.card - ∑ i, ((kml i).1 + (kml i).2.1))) * G x := by
    rw [hΨ]
    funext x
    rw [hGz x, pow_add]
    ring
  refine ⟨?_, ?_⟩
  · rw [hΨ]
    exact (differentiable_pow _).mul hFdiff
  · intro n hn
    rw [hΨ2]
    exact PO.pow_mul_vanish _ G hG n (by omega)
