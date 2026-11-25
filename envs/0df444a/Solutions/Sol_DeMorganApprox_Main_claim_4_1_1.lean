-- Prove2me | solution 1 for DeMorganApprox.Main.claim_4_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:18:00.221808+00:00
-- url     : https://prove2.me/submissions/5872cecb-ff38-4bd9-8d07-9ed03b5d1ed9

import Definitions.Def_DeMorganApprox_Main_Extraction

open DeMorganApprox.Main MvPolynomial

private lemma Lpos {σ : Type} (p : MvPolynomial σ ℝ) : 0 ≤ coeffL1 p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma Ladd {σ : Type} (p q : MvPolynomial σ ℝ) :
    coeffL1 (p + q) ≤ coeffL1 p + coeffL1 q := by
  classical
  let U := p.support ∪ q.support
  have h (r : MvPolynomial σ ℝ) (hr : r.support ⊆ U) :
      coeffL1 r = ∑ i ∈ U, |r.coeff i| := by
    apply Finset.sum_subset hr
    exact fun i _ hi => by simp [notMem_support_iff.mp hi]
  rw [h _ support_add, h _ Finset.subset_union_left, h _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun _ _ => by simpa using abs_add_le _ _

private lemma Lsum {σ α : Type} (s : Finset α) (f : α → MvPolynomial σ ℝ) :
    coeffL1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (Ladd ..).trans (add_le_add (le_refl _) ih)

private lemma Lmono {σ : Type} (i : σ →₀ ℕ) (a : ℝ) :
    coeffL1 (monomial i a) = |a| := by
  classical
  by_cases ha : a = 0 <;> simp [coeffL1, support_monomial, ha]

private lemma Lmul {σ : Type} (p q : MvPolynomial σ ℝ) :
    coeffL1 (p*q) ≤ coeffL1 p * coeffL1 q := by
  classical
  have he : p*q = ∑ i ∈ p.support, ∑ j ∈ q.support,
      monomial (i+j) (p.coeff i*q.coeff j) := by
    conv_lhs => rw [p.as_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    conv_lhs => enter [2]; rw [q.as_sum]
    simp only [Finset.mul_sum, monomial_mul]
  rw [he]
  refine (Lsum _ _).trans ?_
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ => Lsum _ _
    _ = _ := by
      simp only [Lmono, abs_mul]
      rw [coeffL1, coeffL1, Finset.sum_mul]
      simp only [Finset.mul_sum]

private lemma LC {σ : Type} (a : ℝ) : coeffL1 (C a : MvPolynomial σ ℝ) = |a| :=
  Lmono 0 a

private lemma Lsmul {σ : Type} (c : ℝ) (p : MvPolynomial σ ℝ) :
    coeffL1 (c • p) ≤ |c| * coeffL1 p := by
  simpa [← C_mul', LC] using Lmul (C c) p

private lemma Llabel {m : ℕ} (l : Label m) : coeffL1 (labelPoly l) ≤ 2 := by
  have h₁ : coeffL1 (1 : MvPolynomial (Fin m) ℝ) = 1 := by
    simpa using (LC (σ := Fin m) 1)
  have hx (i : Fin m) : coeffL1 (X i : MvPolynomial (Fin m) ℝ) = 1 := by
    simpa [X] using (Lmono (Finsupp.single i 1) (1:ℝ))
  cases l with
  | always => change coeffL1 (1 : MvPolynomial (Fin m) ℝ) ≤ 2; rw [h₁]; norm_num
  | pos i => change coeffL1 (X i : MvPolynomial (Fin m) ℝ) ≤ 2; rw [hx]; norm_num
  | neg i =>
    change coeffL1 (1 - X i : MvPolynomial (Fin m) ℝ) ≤ 2
    have hn (p : MvPolynomial (Fin m) ℝ) : coeffL1 (-p) = coeffL1 p := by simp [coeffL1]
    simpa [sub_eq_add_neg, h₁, hn, hx, show (1:ℝ)+1 = 2 by norm_num] using Ladd (1 : MvPolynomial (Fin m) ℝ) (-X i)

private noncomputable def en {ι : Type} [Fintype ι] (y : ι → ℝ) := Real.sqrt (∑ i, y i ^ 2)

private lemma en_sq {ι : Type} [Fintype ι] (y : ι → ℝ) :
    en y ^ 2 = ∑ i, y i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private lemma en_mono {ι : Type} [Fintype ι] {v w : ι → ℝ} (hv : ∀ i, 0 ≤ v i)
    (h : ∀ i, v i ≤ w i) : en v ≤ en w :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => by gcongr <;> first | exact hv i | exact h i)

private lemma en_scale {ι : Type} [Fintype ι] (v : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    en (fun i => c*v i) = c*en v := by
  simp only [en, mul_pow, ← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

private lemma en_triangle {ι : Type} [Fintype ι] (v w : ι → ℝ) :
    en (fun i => v i+w i) ≤ en v+en w := by
  have h := norm_add_le (WithLp.toLp 2 v : EuclideanSpace ℝ ι) (WithLp.toLp 2 w)
  simpa [en, EuclideanSpace.norm_eq, Real.norm_eq_abs] using h

private lemma transpose_bound {ι J : Type} [Fintype ι] [Fintype J]
    (V : J → ι → ℝ) (K : ℝ) (hK : 0 ≤ K) (h : AbsNormLE V K) (x : ι → ℝ) :
    en (fun j => ∑ i, |V j i| * x i) ≤ K*en x := by
  let z := fun j => ∑ i, |V j i| * x i
  let u := fun i => ∑ j, |V j i| * z j
  have he : en z ^ 2 = ∑ i, x i*u i := by
    rw [en_sq]
    simp_rw [pow_two]
    conv_lhs => enter [2,j,1]; change ∑ i, |V j i| *x i
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [u, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
  have hcs : ∑ i, x i * u i ≤ en x*en u := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hu : en u ≤ K * en z := h z
  have h0 : 0 ≤ en x := Real.sqrt_nonneg _
  have h1 : 0 ≤ en z := Real.sqrt_nonneg _
  by_cases hz : en z = 0
  · change en z ≤ _
    rw [hz]
    positivity
  · change en z ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hu h0, mul_self_pos.mpr hz]

private lemma Ltarget {m : ℕ} (t S : ℝ) (hS : 1 ≤ S) (q : MvPolynomial (Fin m) ℝ) :
    coeffL1 (C (t/(10*Real.sqrt S))*q) ≤ |t| * coeffL1 q := by
  refine (Lmul ..).trans (mul_le_mul_of_nonneg_right ?_ (Lpos q))
  rw [LC, abs_div, abs_of_pos (by positivity : 0 < 10*Real.sqrt S)]
  apply div_le_self (abs_nonneg _)
  have := Real.one_le_sqrt.mpr hS
  linarith

private lemma Lentry {m : ℕ} (v : ℝ) (l : Label m) (q : MvPolynomial (Fin m) ℝ) :
    coeffL1 (C v*labelPoly l*q) ≤ 2*(|v| *coeffL1 q) := by
  refine (Lmul ..).trans ?_
  have hh := (Lmul (C v) (labelPoly l)).trans (mul_le_mul_of_nonneg_left (Llabel l) (Lpos _))
  rw [LC] at hh
  calc
    _ ≤ (|v| *2)*coeffL1 q := mul_le_mul_of_nonneg_right hh (Lpos q)
    _ = _ := by ring

theorem solution (K : ℝ) (hK : 0 ≤ K) :
    ∃ c₀ : ℝ, ∀ cnorm : ℝ, c₀ ≤ cnorm →
      ∀ (m : ℕ) {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
        (P : SpanProgram m ι J), sqNorm P.target = 1 → AbsNormLE P.vec K →
        ∀ S : ℝ, 1 ≤ S → ∀ j : ℕ,
          coeffL1 ((scaledSymbolicMatrix P S cnorm ^ j) (Sum.inl ()) (Sum.inl ())) ≤ 1 := by
  refine ⟨1+2*K, ?_⟩
  intro c hc m ι J _ _ _ _ P hτ hV S hS j
  classical
  let M := scaledSymbolicMatrix P S c
  let o : Unit ⊕ ι ⊕ J := .inl ()
  have hcpos : 0 < c := by linarith
  have hd : 0 ≤ c⁻¹ := (inv_pos.mpr hcpos).le
  have ht : en (fun i => |P.target i|) = 1 := by
    simpa [en, sqNorm] using congrArg Real.sqrt hτ
  have ih : ∀ n : ℕ,
      coeffL1 ((M^n) o o) ≤ 1 ∧
      en (fun i => coeffL1 ((M^n) (.inr (.inl i)) o)) ≤ 1 ∧
      en (fun j => coeffL1 ((M^n) (.inr (.inr j)) o)) ≤ 1 := by
    intro n
    induction n with
    | zero =>
      have h1 : coeffL1 (1 : MvPolynomial (Fin m) ℝ) = 1 := by simpa using (LC (σ := Fin m) 1)
      simp [o, Matrix.one_apply, h1, en, coeffL1]
    | succ n ih =>
      let q := fun a => (M^n) a o
      let u := fun i => coeffL1 (q (.inr (.inl i)))
      let v := fun j => coeffL1 (q (.inr (.inr j)))
      obtain ⟨h₀, hu, hv⟩ := ih
      change coeffL1 (q o) ≤ 1 at h₀
      change en u ≤ 1 at hu
      change en v ≤ 1 at hv
      let U := fun i => ∑ j, |P.vec j i| * v j
      let V := fun j => ∑ i, |P.vec j i| * u i
      have hU : en U ≤ K := (hV v).trans (by simpa [en] using mul_le_mul_of_nonneg_left hv hK)
      have hW : en V ≤ K := (transpose_bound P.vec K hK hV u).trans
        (by simpa using mul_le_mul_of_nonneg_left hu hK)
      have expandM (a : Unit ⊕ ι ⊕ J) :
          (M^(n+1)) a o = c⁻¹ • (∑ b, symbolicMatrix P S a b * q b) := by
        rw [pow_succ', Matrix.mul_apply]
        simp [M, scaledSymbolicMatrix, Matrix.smul_apply, smul_mul_assoc, Finset.smul_sum, q]
      have bound0 : coeffL1 ((M^(n+1)) o o) ≤ c⁻¹ * 1 := by
        rw [expandM]
        simp only [o, Fintype.sum_sum_type, Fintype.sum_unique, symbolicMatrix, zero_mul,
          Finset.sum_const_zero, add_zero, zero_add]
        refine (Lsmul ..).trans ?_
        rw [abs_of_nonneg hd]
        apply mul_le_mul_of_nonneg_left _ hd
        refine (Lsum _ _).trans ((Finset.sum_le_sum (fun i _ => Ltarget _ S hS _)).trans ?_)
        have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |P.target i|) u
        exact hh.trans (by change en (fun i => |P.target i|)*en u ≤ 1; simpa [ht] using hu)
      have boundI (i : ι) :
          coeffL1 ((M^(n+1)) (.inr (.inl i)) o) ≤ c⁻¹*(|P.target i| + 2*U i) := by
        rw [expandM]
        simp only [Fintype.sum_sum_type, Fintype.sum_unique, symbolicMatrix, zero_mul,
          Finset.sum_const_zero, zero_add]
        refine (Lsmul ..).trans ?_
        rw [abs_of_nonneg hd]
        apply mul_le_mul_of_nonneg_left _ hd
        refine (Ladd ..).trans (add_le_add ?_ ?_)
        · exact (Ltarget _ S hS _).trans (by simpa [o] using mul_le_mul_of_nonneg_left h₀ (abs_nonneg (P.target i)))
        · refine (Lsum _ _).trans ((Finset.sum_le_sum (fun j _ => Lentry _ _ _)).trans_eq ?_)
          unfold U
          rw [Finset.mul_sum]
      have boundJ (j : J) :
          coeffL1 ((M^(n+1)) (.inr (.inr j)) o) ≤ c⁻¹*(2*V j) := by
        rw [expandM]
        simp only [Fintype.sum_sum_type, Fintype.sum_unique, symbolicMatrix, zero_mul,
          Finset.sum_const_zero, add_zero, zero_add]
        refine (Lsmul ..).trans ?_
        rw [abs_of_nonneg hd]
        apply mul_le_mul_of_nonneg_left _ hd
        refine (Lsum _ _).trans ((Finset.sum_le_sum (fun i _ => Lentry _ _ _)).trans_eq ?_)
        unfold V
        rw [Finset.mul_sum]
      refine ⟨bound0.trans ?_, (en_mono (fun _ => Lpos _) boundI).trans ?_,
        (en_mono (fun _ => Lpos _) boundJ).trans ?_⟩
      · rw [mul_one]; exact inv_le_one_of_one_le₀ (by linarith)
      · rw [en_scale _ _ hd]
        refine (mul_le_mul_of_nonneg_left (en_triangle (fun i => |P.target i|) (fun i => 2*U i)) hd).trans ?_
        rw [ht, en_scale _ _ (by norm_num)]
        exact (inv_mul_le_iff₀ hcpos).mpr (by linarith)
      · rw [en_scale _ _ hd, en_scale _ _ (by norm_num)]
        exact (inv_mul_le_iff₀ hcpos).mpr (by linarith)
  exact (ih j).1
