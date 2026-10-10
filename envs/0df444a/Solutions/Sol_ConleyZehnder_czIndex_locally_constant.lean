-- Prove2me | solution 1 for ConleyZehnder.czIndex_locally_constant
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T22:33:31.11518+00:00
-- url     : https://prove2.me/submissions/8da451d8-5d86-465f-9aa5-f3c7b934c7cf

import Definitions.Def_ConleyZehnder_Setting
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family

open Matrix Filter Topology Set

/-! Cayley transform between `Sp*` and Hamiltonian matrices without eigenvalue `1`. -/

namespace ConleyZehnder

open Matrix

variable {n : ℕ}

/-- Hamiltonian matrices without eigenvalue `1`. -/
def HamStar (n : ℕ) : Set (Mat n) := {X | X * J₀ n + J₀ n * Xᵀ = 0 ∧ (1 - X).det ≠ 0}

/-- The Cayley transform `(X + 1)(X - 1)⁻¹`. -/
noncomputable def cay (X : Mat n) : Mat n := (X + 1) * (X - 1)⁻¹

lemma det_sub_one_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1).det ≠ 0 := by
  have : X - 1 = -(1 - X) := by abel
  rw [this, Matrix.det_neg]
  simp [Fintype.card_sum, h]

lemma isUnit_det_sub_one {X : Mat n} (h : (1 - X).det ≠ 0) : IsUnit (X - 1).det :=
  isUnit_iff_ne_zero.2 (det_sub_one_ne_zero h)

lemma one_sub_cay {X : Mat n} (h : (1 - X).det ≠ 0) : 1 - cay X = (-2 : ℝ) • (X - 1)⁻¹ := by
  have hu := isUnit_det_sub_one h
  calc 1 - cay X = (X - 1) * (X - 1)⁻¹ - (X + 1) * (X - 1)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hu]; rfl
    _ = (X - 1 - (X + 1)) * (X - 1)⁻¹ := by rw [← Matrix.sub_mul]
    _ = ((-2 : ℝ) • (1 : Mat n)) * (X - 1)⁻¹ := by
        congr 1; rw [show X - 1 - (X + 1) = -((1 : Mat n) + 1) by abel]
        rw [neg_smul, two_smul]
    _ = (-2 : ℝ) • (X - 1)⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]

lemma det_one_sub_cay_ne_zero {X : Mat n} (h : (1 - X).det ≠ 0) : (1 - cay X).det ≠ 0 := by
  rw [one_sub_cay h, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (det_sub_one_ne_zero h))

/-- `(X - 1) cay X = X + 1`. -/
lemma sub_one_mul_cay {X : Mat n} (h : (1 - X).det ≠ 0) : (X - 1) * cay X = X + 1 := by
  have hu := isUnit_det_sub_one h
  have hc : (X - 1) * (X + 1) = (X + 1) * (X - 1) := by noncomm_ring
  unfold cay
  rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

lemma cay_eq_of {X W : Mat n} (h : (1 - X).det ≠ 0) (hW : (X - 1) * W = X + 1) : cay X = W := by
  have hu := isUnit_det_sub_one h
  have e : (X - 1) * cay X = (X - 1) * W := by rw [sub_one_mul_cay h, hW]
  have := congrArg (fun M => (X - 1)⁻¹ * M) e
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] using this

lemma cay_mem_symplectic {X : Mat n} (hH : X * J₀ n + J₀ n * Xᵀ = 0) (h : (1 - X).det ≠ 0) :
    cay X ∈ symplecticGroup (Fin n) ℝ := by
  rw [SymplecticGroup.mem_iff]
  set Q := X - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one h
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay X = X + 1 := sub_one_mul_cay h
  have key : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = Q * J₀ n * Qᵀ := by
    have e1 : Q * (cay X * J₀ n * (cay X)ᵀ) * Qᵀ = (Q * cay X) * J₀ n * (Q * cay X)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (X + 1) * J₀ n * (Xᵀ + 1) - (X - 1) * J₀ n * (Xᵀ - 1)
        = (2 : ℝ) • (X * J₀ n + J₀ n * Xᵀ) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [hH, smul_zero] at this
    exact sub_eq_zero.1 this
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_mem_spStar {X : Mat n} (hX : X ∈ HamStar n) : cay X ∈ SpStar n :=
  ⟨cay_mem_symplectic hX.1 hX.2, det_one_sub_cay_ne_zero hX.2⟩

lemma cay_mem_hamStar {A : Mat n} (hA : A ∈ SpStar n) : cay A ∈ HamStar n := by
  refine ⟨?_, det_one_sub_cay_ne_zero hA.2⟩
  have hS : A * J₀ n * Aᵀ = J₀ n := (SymplecticGroup.mem_iff).1 hA.1
  set Q := A - 1 with hQdef
  have hu : IsUnit Q.det := isUnit_det_sub_one hA.2
  have hut : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  have hQ : Q * cay A = A + 1 := sub_one_mul_cay hA.2
  have key : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ = 0 := by
    have e1 : Q * (cay A * J₀ n + J₀ n * (cay A)ᵀ) * Qᵀ
        = (Q * cay A) * J₀ n * Qᵀ + Q * J₀ n * (Q * cay A)ᵀ := by
      simp [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [e1, hQ, hQdef]
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one]
    have : (A + 1) * J₀ n * (Aᵀ - 1) + (A - 1) * J₀ n * (Aᵀ + 1)
        = (2 : ℝ) • (A * J₀ n * Aᵀ - J₀ n) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, two_smul]
      abel
    rw [this, hS, sub_self, smul_zero]
  have := congrArg (fun M => Q⁻¹ * M * Qᵀ⁻¹) key
  simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
    Matrix.zero_mul, Matrix.mul_zero] at this
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut] using this

lemma cay_cay {A : Mat n} (h : (1 - A).det ≠ 0) : cay (cay A) = A := by
  have hu : IsUnit (A - 1).det := isUnit_det_sub_one h
  have h2 : (1 - cay A).det ≠ 0 := det_one_sub_cay_ne_zero h
  apply cay_eq_of h2
  have hm : cay A - 1 = (2 : ℝ) • (A - 1)⁻¹ := by
    rw [show cay A - 1 = -(1 - cay A) by abel, one_sub_cay h, neg_smul, neg_neg]
  have hL : (A - 1)⁻¹ * A = 1 + (A - 1)⁻¹ := by
    rw [show (A - 1)⁻¹ * A = (A - 1)⁻¹ * ((A - 1) + 1) by rw [sub_add_cancel]]
    rw [Matrix.mul_add, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  rw [hm, Matrix.smul_mul, hL, show cay A + 1 = (cay A - 1) + (1 + 1) by abel, hm,
    smul_add, two_smul ℝ (1 : Mat n)]
  abel

lemma continuousOn_cay : ContinuousOn (cay (n := n)) {X | (1 - X).det ≠ 0} := by
  have hs : Continuous fun X : Mat n => X - 1 := continuous_id.sub continuous_const
  have hp : Continuous fun X : Mat n => X + 1 := continuous_id.add continuous_const
  have hd : Continuous fun X : Mat n => (X - 1).det := hs.matrix_det
  have hinv : ContinuousOn (fun X : Mat n => ((X - 1).det)⁻¹) {X | (1 - X).det ≠ 0} :=
    hd.continuousOn.inv₀ fun X hX => det_sub_one_ne_zero hX
  have hadj : Continuous fun X : Mat n => (X - 1).adjugate := hs.matrix_adjugate
  refine (hp.continuousOn.mul (hinv.smul hadj.continuousOn)).congr ?_
  intro X _
  simp [cay, Matrix.inv_def, Ring.inverse_eq_inv']

lemma cay_zero : cay (0 : Mat n) = Wplus n := by
  apply cay_eq_of (by simp)
  simp [Wplus]

/-- The Hamiltonian counterpart of `W⁻`. -/
noncomputable def Yminus (n : ℕ) : Mat n :=
  Matrix.diagonal (Sum.elim (fun j : Fin n => if j.val = 0 then (3 : ℝ) else 0)
    (fun j : Fin n => if j.val = 0 then (-3 : ℝ) else 0))

lemma det_one_sub_Yminus : (1 - Yminus n).det ≠ 0 := by
  unfold Yminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma cay_Yminus : cay (Yminus n) = Wminus n := by
  apply cay_eq_of det_one_sub_Yminus
  unfold Yminus Wminus
  rw [show (1 : Mat n) = Matrix.diagonal 1 from rfl, Matrix.diagonal_sub, Matrix.diagonal_add,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with j | j <;> by_cases hj : j.val = 0 <;> simp [hj] <;> norm_num

lemma Yminus_ham : Yminus n * J₀ n + J₀ n * (Yminus n)ᵀ = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Yminus, Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply,
      Matrix.one_apply] <;>
    (rcases eq_or_ne i j with rfl | h <;> simp [*] <;> split_ifs <;> norm_num)

lemma Yminus_mem : Yminus n ∈ HamStar n := ⟨Yminus_ham, det_one_sub_Yminus⟩

lemma zero_mem_hamStar : (0 : Mat n) ∈ HamStar n := ⟨by simp, by simp⟩

/-- Transport: a path in `HamStar` from `cay A` to `0` or `Yminus` gives the target. -/
theorem spStar_path_of_hamStar {A : Mat n} (hA : A ∈ SpStar n)
    (h : JoinedIn (HamStar n) (cay A) 0 ∨ JoinedIn (HamStar n) (cay A) (Yminus n)) :
    ∃ χ : C(unitInterval, Mat n), χ 0 = A ∧ (∀ t, χ t ∈ SpStar n) ∧
      (χ 1 = Wplus n ∨ χ 1 = Wminus n) := by
  have hmap : ∀ {Y : Mat n}, JoinedIn (HamStar n) (cay A) Y →
      JoinedIn (SpStar n) A (cay Y) := by
    intro Y hY
    have := hY.map_continuousOn (f := cay) (continuousOn_cay.mono fun X hX => hX.2)
    rw [cay_cay hA.2] at this
    exact this.mono (Set.image_subset_iff.2 fun X hX => cay_mem_spStar hX)
  rcases h with h | h
  · have hj := hmap h
    rw [cay_zero] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inl (by simp)⟩
  · have hj := hmap h
    rw [cay_Yminus] at hj
    exact ⟨hj.somePath, by simp, hj.somePath_mem, Or.inr (by simp)⟩

end ConleyZehnder

namespace ConleyZehnder

namespace CZ11

variable {n : ℕ}

/-- `A⁻¹ = -J₀ Aᵀ J₀` written as a polynomial expression. -/
noncomputable def sinv (A : Mat n) : Mat n := -J₀ n * Aᵀ * J₀ n

theorem sinv_mul {A : Mat n} (hA : IsSymplectic A) : sinv A * A = 1 := by
  have := SymplecticGroup.inv_left_mul_aux hA
  rw [← this]; simp only [sinv, Matrix.neg_mul]

theorem mul_sinv {A : Mat n} (hA : IsSymplectic A) : A * sinv A = 1 :=
  mul_eq_one_comm.mp (sinv_mul hA)

theorem sinv_symp {A : Mat n} (hA : IsSymplectic A) : IsSymplectic (sinv A) :=
  (⟨A, hA⟩⁻¹ : Matrix.symplecticGroup (Fin n) ℝ).2

theorem neg_symp {A : Mat n} (hA : IsSymplectic A) : IsSymplectic (-A) :=
  SymplecticGroup.neg_mem hA

theorem mul_symp {A B : Mat n} (hA : IsSymplectic A) (hB : IsSymplectic B) :
    IsSymplectic (A * B) := Submonoid.mul_mem _ hA hB

theorem continuous_sinv : Continuous (sinv (n := n)) := by
  unfold sinv; fun_prop

/-- The deformation from `1` to `D` inside `Sp`: `F s D = -cay (s • cay (-D))`. -/
noncomputable def F (s : ℝ) (D : Mat n) : Mat n := -cay (s • cay (-D))

theorem det_one_sub_neg_one : (1 - -(1 : Mat n)).det ≠ 0 := by
  have e : (1 : Mat n) - -1 = (2 : ℝ) • 1 := by rw [sub_neg_eq_add, two_smul]
  rw [e, det_smul, det_one, mul_one]; exact pow_ne_zero _ two_ne_zero

theorem cay_neg_one : cay (-1 : Mat n) = 0 := by
  apply cay_eq_of det_one_sub_neg_one
  simp

theorem F_zero (D : Mat n) : F 0 D = 1 := by
  simp [F, cay_zero, Wplus]

theorem F_one {D : Mat n} (hD : (1 - -D).det ≠ 0) : F 1 D = D := by
  simp [F, cay_cay hD]

theorem F_at_one (s : ℝ) : F s (1 : Mat n) = 1 := by
  simp [F, cay_neg_one, cay_zero, Wplus]

theorem F_symp {s : ℝ} {D : Mat n} (hD : IsSymplectic D) (h1 : (1 - -D).det ≠ 0)
    (h2 : (1 - s • cay (-D)).det ≠ 0) : IsSymplectic (F s D) := by
  have hY := cay_mem_hamStar (A := -D) ⟨neg_symp hD, h1⟩
  have hH : (s • cay (-D)) * J₀ n + J₀ n * (s • cay (-D))ᵀ = 0 := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hY.1, smul_zero]
  exact neg_symp (cay_mem_symplectic hH h2)

/-- The good set of `(D, s)`. -/
def Good (P : Mat n) (D : Mat n) (s : ℝ) : Prop :=
  (1 - -D).det ≠ 0 ∧ (1 - s • cay (-D)).det ≠ 0 ∧ (1 - P * F s D).det ≠ 0

theorem continuousAt_cay {X : Mat n} (h : (1 - X).det ≠ 0) : ContinuousAt (cay (n := n)) X := by
  refine continuousOn_cay.continuousAt (IsOpen.mem_nhds ?_ h)
  exact isOpen_ne_fun (continuous_const.sub continuous_id).matrix_det continuous_const

theorem eventually_good (P : Mat n) (hP : (1 - P).det ≠ 0) :
    ∀ᶠ D in 𝓝 (1 : Mat n), ∀ s ∈ Icc (0 : ℝ) 1, Good P D s := by
  refine isCompact_Icc.eventually_forall_of_forall_eventually fun s _ => ?_
  have hdet : Continuous fun M : Mat n => M.det := continuous_id.matrix_det
  have hc1 : ContinuousAt (fun z : Mat n × ℝ => cay (-z.1)) (1, s) :=
    ContinuousAt.comp (g := cay) (f := fun z : Mat n × ℝ => -z.1)
      (continuousAt_cay det_one_sub_neg_one) continuous_fst.neg.continuousAt
  have hc2 : ContinuousAt (fun z : Mat n × ℝ => z.2 • cay (-z.1)) (1, s) :=
    continuous_snd.continuousAt.smul hc1
  have hv2 : (1 - s • cay (-1 : Mat n)).det ≠ 0 := by
    rw [cay_neg_one, smul_zero, sub_zero, det_one]; exact one_ne_zero
  have hc3 : ContinuousAt (fun z : Mat n × ℝ => cay (z.2 • cay (-z.1))) (1, s) :=
    ContinuousAt.comp (g := cay) (f := fun z : Mat n × ℝ => z.2 • cay (-z.1))
      (continuousAt_cay hv2) hc2
  have e1 : ∀ᶠ z in 𝓝 ((1 : Mat n), s), (1 - -z.1).det ≠ 0 :=
    (hdet.comp (continuous_const.sub continuous_fst.neg)).continuousAt.eventually_ne
      det_one_sub_neg_one
  have e2 : ∀ᶠ z in 𝓝 ((1 : Mat n), s), (1 - z.2 • cay (-z.1)).det ≠ 0 :=
    (hdet.continuousAt.comp (continuousAt_const.sub hc2)).eventually_ne hv2
  have e3 : ∀ᶠ z in 𝓝 ((1 : Mat n), s), (1 - P * F z.2 z.1).det ≠ 0 := by
    have hF : ContinuousAt (fun z : Mat n × ℝ => F z.2 z.1) (1, s) := hc3.neg
    refine (hdet.continuousAt.comp (continuousAt_const.sub (continuousAt_const.mul hF))).eventually_ne ?_
    simpa [Function.comp_def, F_at_one] using hP
  filter_upwards [e1, e2, e3] with z h1 h2 h3 using ⟨h1, h2, h3⟩

theorem czIndex_locally_constant (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    ∀ᶠ ψ' in 𝓝 ψ, ψ' ∈ SP n → czIndex ψ' = czIndex ψ := by
  obtain ⟨hsy, h0, h1⟩ := hψ
  obtain ⟨U, hUV, hUo, h1U⟩ := mem_nhds_iff.1 (eventually_good (ψ 1) h1)
  let Pinv : C(unitInterval, Mat n) := ⟨fun t => sinv (ψ t), continuous_sinv.comp ψ.continuous⟩
  have hPψ : MapsTo (Pinv * ψ) univ U := fun t _ => by
    show sinv (ψ t) * ψ t ∈ U
    rw [sinv_mul (hsy t)]; exact h1U
  have hcont : Continuous fun g : C(unitInterval, Mat n) => Pinv * g :=
    continuous_const.mul continuous_id
  have hev : ∀ᶠ g in 𝓝 ψ, MapsTo (⇑(Pinv * g)) univ U :=
    hcont.continuousAt.eventually (ContinuousMap.eventually_mapsTo isCompact_univ hUo hPψ)
  filter_upwards [hev] with ψ' hψ' hSP
  obtain ⟨hsy', h0', h1'⟩ := hSP
  set D : unitInterval → Mat n := fun t => sinv (ψ t) * ψ' t with hD
  have hDc : Continuous D := (continuous_sinv.comp ψ.continuous).mul ψ'.continuous
  have hDs : ∀ t, IsSymplectic (D t) := fun t => mul_symp (sinv_symp (hsy t)) (hsy' t)
  have hG : ∀ t, ∀ s ∈ Icc (0 : ℝ) 1, Good (ψ 1) (D t) s := fun t => hUV (hψ' (mem_univ t))
  have hcay1 : Continuous fun p : unitInterval × unitInterval => cay (-D p.2) :=
    continuousOn_cay.comp_continuous (hDc.comp continuous_snd).neg
      fun p => (hG p.2 0 ⟨le_rfl, zero_le_one⟩).1
  have hcay2 : Continuous fun p : unitInterval × unitInterval => cay ((p.1 : ℝ) • cay (-D p.2)) :=
    continuousOn_cay.comp_continuous ((continuous_subtype_val.comp continuous_fst).smul hcay1)
      fun p => (hG p.2 p.1 p.1.2).2.1
  let H : C(unitInterval × unitInterval, Mat n) :=
    ⟨fun p => ψ p.2 * F p.1 (D p.2), (ψ.continuous.comp continuous_snd).mul hcay2.neg⟩
  have hD0 : D 0 = 1 := by
    simp only [hD]; rw [h0', mul_one, ← sinv_mul (hsy 0), h0, mul_one]
  refine czIndex_eq_of_family H
    (fun s t => mul_symp (hsy t) (F_symp (hDs t) (hG t s s.2).1 (hG t s s.2).2.1))
    (fun s => ?_) (fun s => (hG 1 s s.2).2.2) ψ ψ' (fun t => ?_) (fun t => ?_)
  · show ψ 0 * F s (D 0) = 1
    rw [hD0, F_at_one, h0, mul_one]
  · show ψ t = ψ t * F ((0 : unitInterval) : ℝ) (D t)
    rw [Set.Icc.coe_zero, F_zero, mul_one]
  · show ψ' t = ψ t * F ((1 : unitInterval) : ℝ) (D t)
    rw [Set.Icc.coe_one, F_one (hG t 1 ⟨zero_le_one, le_rfl⟩).1]
    simp only [hD]; rw [← mul_assoc, mul_sinv (hsy t), one_mul]

end CZ11

end ConleyZehnder

open ConleyZehnder

open Filter Topology

theorem solution {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    ∀ᶠ ψ' in 𝓝 ψ, ψ' ∈ SP n → czIndex ψ' = czIndex ψ :=
  ConleyZehnder.CZ11.czIndex_locally_constant ψ hψ
