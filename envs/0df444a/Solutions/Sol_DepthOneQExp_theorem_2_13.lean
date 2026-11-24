-- Prove2me | solution 1 for DepthOneQExp.theorem_2_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:56:20.146655+00:00
-- url     : https://prove2.me/submissions/c3990968-9ff2-4efc-a80d-81a85a211426

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_permToMatrix
import Definitions.Def_DepthOneQExp_xPerm
import Definitions.Def_DepthOneQExp_zMat
import Definitions.Def_DepthOneQExp_cnotGroup
import Definitions.Def_DepthOneQExp_cnotAvg
import Definitions.Def_DepthOneQExp_IsQuantumExpanderGap
import Definitions.Def_DepthOneQExp_maxEnt
import Definitions.Def_DepthOneQExp_piProj
import Definitions.Def_DepthOneQExp_hOp
import Theorems.Thm_DepthOneQExp_eq_2_45
import Theorems.Thm_DepthOneQExp_hh09_lemma1

open DepthOneQExp Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace DepthOneQExp.Thm213Aux

variable {n : ℕ}

abbrev κ (n : ℕ) := MITMSynthesis.Q n × MITMSynthesis.Q n

theorem kron_perm {α : Type} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permToMatrix σ ⊗ₖ permToMatrix τ = permToMatrix (Equiv.prodCongr σ τ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, permToMatrix, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h1 : a = σ c <;> by_cases h2 : b = τ d <;> simp [h1, h2]

theorem permToMatrix_map_star {α : Type} [DecidableEq α] (σ : Equiv.Perm α) :
    (permToMatrix σ).map star = permToMatrix σ := by
  ext a b; simp only [map_apply, permToMatrix]; split_ifs <;> simp

theorem zMat_map_star (j : ℕ) : (zMat n j).map star = zMat n j := by
  ext a b; simp only [map_apply, zMat, diagonal_apply]; split_ifs <;> simp

theorem zMat_kron : zMat n 0 ⊗ₖ zMat n 0 =
    diagonal (fun p : κ n => (if bit p.1 0 = 1 then -1 else 1) * (if bit p.2 0 = 1 then -1 else 1)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, zMat, diagonal_apply, Prod.mk.injEq]
  by_cases h1 : a = c <;> by_cases h2 : b = d <;> simp [h1, h2]

theorem zz_unitary : zMat n 0 ⊗ₖ zMat n 0 ∈ unitaryGroup (κ n) ℂ := by
  rw [zMat_kron, mem_unitaryGroup_iff']
  rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext p
  by_cases h1 : bit p.1 0 = 1 <;> by_cases h2 : bit p.2 0 = 1 <;> simp [h1, h2]

/-- the vector `a₁` is fixed by permutations of the form `σ × σ` -/
theorem perm_mulVec_maxEnt (σ : Equiv.Perm (MITMSynthesis.Q n)) :
    permToMatrix (Equiv.prodCongr σ σ) *ᵥ maxEnt n = maxEnt n := by
  funext ⟨x, y⟩
  simp only [mulVec, dotProduct, permToMatrix, maxEnt, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ((Equiv.prodCongr σ σ).symm (x, y))]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; apply hb; rw [h, Equiv.symm_apply_apply]
  · simp

theorem zz_mulVec_maxEnt : (zMat n 0 ⊗ₖ zMat n 0) *ᵥ maxEnt n = maxEnt n := by
  rw [zMat_kron]
  funext ⟨x, y⟩
  simp only [mulVec_diagonal, maxEnt]
  by_cases hxy : x = y
  · subst hxy
    by_cases h1 : bit x 0 = 1 <;> simp [h1]
  · simp [hxy]

noncomputable def phi (n : ℕ) : Matrix (κ n) (κ n) ℂ :=
  (1 / (2 ^ n : ℂ)) • vecMulVec (maxEnt n) (star (maxEnt n))

theorem maxEnt_dot : star (maxEnt n) ⬝ᵥ maxEnt n = 2 ^ n := by
  simp only [dotProduct, maxEnt, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq, MITMSynthesis.Q]

theorem mul_phi (U : Matrix (κ n) (κ n) ℂ) (h : U *ᵥ maxEnt n = maxEnt n) : U * phi n = phi n := by
  rw [phi, Matrix.mul_smul, mul_vecMulVec, h]

theorem phi_mul (U : Matrix (κ n) (κ n) ℂ) (h : Uᴴ *ᵥ maxEnt n = maxEnt n) : phi n * U = phi n := by
  rw [phi, Matrix.smul_mul, vecMulVec_mul]
  congr 2
  have := congrArg star h
  rw [star_mulVec, conjTranspose_conjTranspose] at this
  exact this

theorem phi_mul_phi : phi n * phi n = phi n := by
  rw [phi, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, maxEnt_dot, smul_smul]
  rw [vecMulVec_smul]
  rw [smul_smul]
  congr 1
  have : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp

theorem phi_herm : (phi n)ᴴ = phi n := by
  rw [phi, conjTranspose_smul, conjTranspose_vecMulVec, star_star]
  congr 1
  simp [star_div₀]

noncomputable def Wm (σ : Equiv.Perm (MITMSynthesis.Q n)) : Matrix (κ n) (κ n) ℂ :=
  permToMatrix (Equiv.prodCongr σ σ)

theorem permToMatrix_conjTranspose {α : Type} [DecidableEq α] (σ : Equiv.Perm α) :
    (permToMatrix σ)ᴴ = permToMatrix σ⁻¹ := by
  ext y x
  simp only [conjTranspose_apply, permToMatrix]
  have : (x = σ y) ↔ (y = σ⁻¹ x) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  by_cases h : x = σ y
  · rw [if_pos h, if_pos (this.1 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp

theorem Wm_conjTranspose (σ : Equiv.Perm (MITMSynthesis.Q n)) : (Wm σ)ᴴ = Wm σ⁻¹ := by
  rw [Wm, permToMatrix_conjTranspose]; rfl

theorem Wm_mul (σ τ : Equiv.Perm (MITMSynthesis.Q n)) : Wm σ * Wm τ = Wm (σ * τ) := by
  rw [Wm, Wm, ← permToMatrix_mul]; rfl

theorem Wm_unitary (σ : Equiv.Perm (MITMSynthesis.Q n)) : Wm σ ∈ unitaryGroup (κ n) ℂ :=
  permToMatrix_mem_unitaryGroup _

theorem Wm_mul_phi (σ : Equiv.Perm (MITMSynthesis.Q n)) : Wm σ * phi n = phi n :=
  mul_phi _ (perm_mulVec_maxEnt σ)

theorem phi_mul_Wm (σ : Equiv.Perm (MITMSynthesis.Q n)) : phi n * Wm σ = phi n := by
  apply phi_mul
  rw [Wm_conjTranspose]
  exact perm_mulVec_maxEnt σ⁻¹

theorem cnotAvg_eq : cnotAvg n = (1 / (Fintype.card (cnotGroup n) : ℂ)) •
    ∑ g : cnotGroup n, Wm (g : Equiv.Perm (MITMSynthesis.Q n)) := by
  simp only [cnotAvg, Wm, kron_perm]

theorem card_ne : (Fintype.card (cnotGroup n) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

theorem Wm_mul_cnotAvg (h : cnotGroup n) : Wm (h : Equiv.Perm (MITMSynthesis.Q n)) * cnotAvg n = cnotAvg n := by
  rw [cnotAvg_eq, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  simp_rw [Wm_mul]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : cnotGroup n => Wm (g : Equiv.Perm (MITMSynthesis.Q n)))

theorem cnotAvg_mul_Wm (h : cnotGroup n) : cnotAvg n * Wm (h : Equiv.Perm (MITMSynthesis.Q n)) = cnotAvg n := by
  rw [cnotAvg_eq, Matrix.smul_mul, Finset.sum_mul]
  congr 1
  simp_rw [Wm_mul]
  exact Equiv.sum_comp (Equiv.mulRight h) (fun g : cnotGroup n => Wm (g : Equiv.Perm (MITMSynthesis.Q n)))

theorem cnotAvg_herm : (cnotAvg n)ᴴ = cnotAvg n := by
  rw [cnotAvg_eq, conjTranspose_smul, conjTranspose_sum]
  simp_rw [Wm_conjTranspose]
  congr 1
  · simp
  · exact Equiv.sum_comp (Equiv.inv (cnotGroup n)) (fun g : cnotGroup n => Wm (g : Equiv.Perm (MITMSynthesis.Q n)))

theorem cnotAvg_idem : cnotAvg n * cnotAvg n = cnotAvg n := by
  nth_rewrite 1 [cnotAvg_eq]
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp_rw [Wm_mul_cnotAvg]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem cnotAvg_mul_phi : cnotAvg n * phi n = phi n := by
  rw [cnotAvg_eq, Matrix.smul_mul, Finset.sum_mul]
  simp_rw [Wm_mul_phi]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem phi_mul_cnotAvg : phi n * cnotAvg n = phi n := by
  rw [cnotAvg_eq, Matrix.mul_smul, Finset.mul_sum]
  simp_rw [phi_mul_Wm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem proj_norm_le {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ) (h1 : Qᴴ = Q)
    (h2 : Q * Q = Q) : ‖Q‖ ≤ 1 := by
  have := CStarRing.norm_star_mul_self (x := Q)
  rw [star_eq_conjTranspose, h1, h2] at this
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg Q]

theorem unitary_norm_le {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) : ‖U‖ ≤ 1 :=
  le_of_eq (CStarRing.norm_coe_unitary (⟨U, hU⟩ : unitary (Matrix ι ι ℂ)))

theorem one_sub_phi_norm : ‖(1 : Matrix (κ n) (κ n) ℂ) - phi n‖ ≤ 1 := by
  apply proj_norm_le
  · rw [conjTranspose_sub, conjTranspose_one, phi_herm]
  · rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, phi_mul_phi]; abel

theorem unitary_sub_phi_norm (U : Matrix (κ n) (κ n) ℂ) (hU : U ∈ unitaryGroup (κ n) ℂ)
    (hUa : U * phi n = phi n) : ‖U - phi n‖ ≤ 1 := by
  have : U - phi n = U * (1 - phi n) := by rw [mul_sub, mul_one, hUa]
  rw [this]
  exact (norm_mul_le _ _).trans (by
    have := unitary_norm_le U hU
    have := one_sub_phi_norm (n := n)
    nlinarith [norm_nonneg U, norm_nonneg ((1 : Matrix (κ n) (κ n) ℂ) - phi n)])

/-- the average of `k ≥ 1` matrices of the form `U - φ` with `‖U - φ‖ ≤ 1` has norm `≤ 1` -/
theorem avg_norm_le {k : ℕ} (hk : 0 < k) (F : Fin k → Matrix (κ n) (κ n) ℂ)
    (hF : ∀ i, ‖F i‖ ≤ 1) : ‖(1 / (k : ℂ)) • ∑ i, F i‖ ≤ 1 := by
  rw [norm_smul]
  have h1 : ‖∑ i, F i‖ ≤ k := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖F i‖ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum fun i _ => hF i
      _ = k := by simp
  have h2 : ‖(1 / (k : ℂ))‖ = 1 / k := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [h2]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_mul_eq_mul_div, one_mul, div_le_one hk']
  exact h1

end DepthOneQExp.Thm213Aux

open DepthOneQExp.Thm213Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) (m : ℕ) (P : Fin m → cnotGroup n) (ε : ℝ)
    (hP : ‖(1 / (m : ℂ)) • ∑ i, (permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ
        permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n))) - cnotAvg n‖ ≤ 1 - ε) :
    IsQuantumExpanderGap
      (Fin.append (fun i => permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n)))
        ![permToMatrix (xPerm n 0), zMat n 0])
      (min (m * ε) 2 / (24 * (m + 2))) := by
  unfold IsQuantumExpanderGap
  -- rewrite the family average
  set V := Fin.append (fun i => permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n)))
        ![permToMatrix (xPerm n 0), zMat n 0] with hV
  set Hx : Matrix (κ n) (κ n) ℂ := Wm (xPerm n 0)
  set Hz : Matrix (κ n) (κ n) ℂ := zMat n 0 ⊗ₖ zMat n 0
  have hsum : ∑ j, V j ⊗ₖ (V j).map star =
      ∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n)) + (Hx + Hz) := by
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hV, Fin.append_left, permToMatrix_map_star, kron_perm]; rfl
    · rw [Fin.sum_univ_two]
      simp only [hV, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
        permToMatrix_map_star, zMat_map_star, kron_perm]
      rfl
  have hphi : (1 / (2 ^ n : ℂ)) • vecMulVec (maxEnt n) (star (maxEnt n)) = phi n := rfl
  rw [hsum, hphi]
  have hCS : cnotAvg n * ∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n)) = (m : ℂ) • cnotAvg n := by
    rw [Finset.mul_sum]; simp_rw [cnotAvg_mul_Wm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hSC : (∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n))) * cnotAvg n = (m : ℂ) • cnotAvg n := by
    rw [Finset.sum_mul]; simp_rw [Wm_mul_cnotAvg]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hφS : phi n * ∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n)) = (m : ℂ) • phi n := by
    rw [Finset.mul_sum]; simp_rw [phi_mul_Wm]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hSφ : (∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n))) * phi n = (m : ℂ) • phi n := by
    rw [Finset.sum_mul]; simp_rw [Wm_mul_phi]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  have hCφ : cnotAvg n * phi n = phi n := cnotAvg_mul_phi
  have hφC : phi n * cnotAvg n = phi n := phi_mul_cnotAvg
  have hCC : cnotAvg n * cnotAvg n = cnotAvg n := cnotAvg_idem
  have hφφ : phi n * phi n = phi n := phi_mul_phi
  have hCh : (cnotAvg n)ᴴ = cnotAvg n := cnotAvg_herm
  have hφh : (phi n)ᴴ = phi n := phi_herm
  set S := ∑ i, Wm (P i : Equiv.Perm (MITMSynthesis.Q n)) with hS
  set C := cnotAvg n
  set φ := phi n
  have hHxφ : Hx * φ = φ := Wm_mul_phi _
  have hφHx : φ * Hx = φ := phi_mul_Wm _
  have hHzφ : Hz * φ = φ := mul_phi _ zz_mulVec_maxEnt
  have hφHz : φ * Hz = φ := by
    apply phi_mul
    have : Hzᴴ = Hz := by
      simp only [Hz, zMat_kron, diagonal_conjTranspose]
      congr 1; funext p
      by_cases h1 : bit p.1 0 = 1 <;> by_cases h2 : bit p.2 0 = 1 <;> simp [h1, h2]
    rw [this]; exact zz_mulVec_maxEnt
  have hHz_u : Hz ∈ unitaryGroup (κ n) ℂ := zz_unitary
  -- the trivial bound
  have htriv : ‖(1 / ((m + 2 : ℕ) : ℂ)) • (S + (Hx + Hz)) - φ‖ ≤ 1 := by
    have : (1 / ((m + 2 : ℕ) : ℂ)) • (S + (Hx + Hz)) - φ =
        (1 / ((m + 2 : ℕ) : ℂ)) • ∑ j : Fin (m + 2),
          (Fin.append (fun i => Wm (P i : Equiv.Perm (MITMSynthesis.Q n))) ![Hx, Hz] j - φ) := by
      rw [Finset.sum_sub_distrib, Fin.sum_univ_add, Fin.sum_univ_two]
      simp only [Fin.append_left, Fin.append_right, Matrix.cons_val_zero, Matrix.cons_val_one,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub, ← hS]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      have : (1 / ((m + 2 : ℕ) : ℂ)) * ((m + 2 : ℕ) : ℂ) = 1 := by
        rw [one_div, inv_mul_cancel₀]; exact_mod_cast (Nat.succ_ne_zero (m + 1))
      rw [this, one_smul]
    rw [this]
    apply avg_norm_le (by omega)
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      exact unitary_sub_phi_norm _ (Wm_unitary _) (Wm_mul_phi _)
    · rw [Fin.append_right]
      fin_cases i
      · exact unitary_sub_phi_norm _ (Wm_unitary _) hHxφ
      · exact unitary_sub_phi_norm _ hHz_u hHzφ
  by_cases hg : min (m * ε) 2 / (24 * (m + 2)) ≤ 0
  · exact htriv.trans (by linarith)
  push Not at hg
  have hm2 : (0 : ℝ) < m + 2 := by positivity
  have hmin : 0 < min ((m : ℝ) * ε) 2 := by
    by_contra h; push Not at h
    exact absurd hg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg h (by positivity)))
  have hmε : 0 < (m : ℝ) * ε := lt_of_lt_of_le hmin (min_le_left _ _)
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hmε
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hε0 : 0 < ε := pos_of_mul_pos_right hmε hmR.le
  have hε1 : ε ≤ 1 := by linarith [norm_nonneg ((1 / (m : ℂ)) • ∑ i, (permToMatrix
    (P i : Equiv.Perm (MITMSynthesis.Q n)) ⊗ₖ permToMatrix (P i : Equiv.Perm (MITMSynthesis.Q n))) - C)]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hPdef : piProj n = C - φ := rfl
  have hHdef : hOp n = Hx + Hz := by rw [hOp, kron_perm]; rfl
  have hP2 : (C - φ) * (C - φ) = C - φ := by
    rw [sub_mul, mul_sub, mul_sub, hCC, hCφ, hφC, hφφ]; abel
  have hPh : (C - φ).IsHermitian := by
    rw [IsHermitian, conjTranspose_sub, hCh, hφh]
  have hXn : ‖(1 / (m : ℂ)) • S - φ‖ ≤ 1 := by
    have : (1 / (m : ℂ)) • S - φ = (1 / (m : ℂ)) • ∑ i, (Wm (P i : Equiv.Perm (MITMSynthesis.Q n)) - φ) := by
      rw [Finset.sum_sub_distrib, smul_sub, ← hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div, inv_mul_cancel₀ hmC, one_smul]
    rw [this]
    exact avg_norm_le hm _ fun i => unitary_sub_phi_norm _ (Wm_unitary _) (Wm_mul_phi _)
  have hYn : ‖(1 / 2 : ℂ) • (Hx + Hz) - φ‖ ≤ 1 := by
    have : (1 / 2 : ℂ) • (Hx + Hz) - φ = (1 / ((2 : ℕ) : ℂ)) • ∑ j : Fin 2, (![Hx, Hz] j - φ) := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_ofNat]
      module
    rw [this]
    apply avg_norm_le (by norm_num)
    intro j; fin_cases j
    · exact unitary_sub_phi_norm _ (Wm_unitary _) hHxφ
    · exact unitary_sub_phi_norm _ hHz_u hHzφ
  have hPX : (C - φ) * ((1 / (m : ℂ)) • S - φ) = C - φ := by
    simp only [mul_sub, sub_mul, Matrix.mul_smul, hCS, hφS, hCφ, hφφ]
    match_scalars <;> field_simp <;> ring
  have hXP : ((1 / (m : ℂ)) • S - φ) * (C - φ) = C - φ := by
    simp only [mul_sub, sub_mul, Matrix.smul_mul, hSC, hSφ, hφC, hφφ]
    match_scalars <;> field_simp <;> ring
  have hX' : ‖(1 - (C - φ)) * ((1 / (m : ℂ)) • S - φ) * (1 - (C - φ))‖ ≤ 1 - ε := by
    have e : (1 - (C - φ)) * ((1 / (m : ℂ)) • S - φ) * (1 - (C - φ)) = (1 / (m : ℂ)) • S - C := by
      rw [sub_mul, one_mul, hPX, mul_sub, mul_one, sub_mul, hXP, hP2]
      abel
    rw [e]
    simpa only [hS, Wm, kron_perm] using hP
  have hY' : ‖(C - φ) * ((1 / 2 : ℂ) • (Hx + Hz) - φ) * (C - φ)‖ ≤ 1 - 1 / 2 := by
    have hPφ : (C - φ) * φ = 0 := by rw [sub_mul, hCφ, hφφ, sub_self]
    have e : (C - φ) * ((1 / 2 : ℂ) • (Hx + Hz) - φ) * (C - φ) =
        (1 / 2 : ℂ) • (piProj n * hOp n * piProj n) := by
      have h1 : (C - φ) * ((1 / 2 : ℂ) • (Hx + Hz) - φ) = (1 / 2 : ℂ) • ((C - φ) * (Hx + Hz)) := by
        rw [mul_sub, hPφ, sub_zero, Matrix.mul_smul]
      rw [h1, Matrix.smul_mul, hPdef, hHdef]
    rw [e, norm_smul, eq_2_45 n hn]
    have h2 : (4 : ℝ) ≤ 2 ^ n := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have : ((2 : ℝ) ^ n - 2) / (2 ^ n - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith [mul_le_mul_of_nonneg_left this (by norm_num : (0:ℝ) ≤ 1 / 2)]
  set p : ℝ := m / (m + 2) with hp
  have hp01 : p ∈ Set.Ioo (0 : ℝ) 1 := ⟨by positivity, by rw [hp, div_lt_one hm2]; linarith⟩
  have key := hh09_lemma1 (C - φ) ((1 / (m : ℂ)) • S - φ) ((1 / 2 : ℂ) • (Hx + Hz) - φ) hP2 hPh hXn hYn
    ε (1 / 2) ⟨hε0, hε1⟩ ⟨by norm_num, by norm_num⟩ hPX hXP hX' hY' p hp01
  have hcomb : (p : ℂ) • ((1 / (m : ℂ)) • S - φ) + ((1 - p : ℝ) : ℂ) • ((1 / 2 : ℂ) • (Hx + Hz) - φ) =
      (1 / ((m + 2 : ℕ) : ℂ)) • (S + (Hx + Hz)) - φ := by
    have hm2C : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (m + 1))
    simp only [hp]
    push_cast
    match_scalars <;> field_simp <;> ring
  rw [hcomb] at key
  refine key.trans (le_of_eq ?_)
  rw [hp]
  have : min ((m : ℝ) / (m + 2) * ε) (1 - m / (m + 2)) = min ((m : ℝ) * ε) 2 / (m + 2) := by
    rw [← min_div_div_right hm2.le]
    congr 1
    · field_simp
    · field_simp; ring
  rw [this]
  field_simp
  ring
