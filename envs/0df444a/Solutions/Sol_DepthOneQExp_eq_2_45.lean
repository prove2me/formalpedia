-- Prove2me | solution 1 for DepthOneQExp.eq_2_45
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:57:47.245795+00:00
-- url     : https://prove2.me/submissions/1722b678-eef5-41d0-b52c-66ab65721ede

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_piProj
import Definitions.Def_DepthOneQExp_hOp
import Definitions.Def_DepthOneQExp_aVec
import Definitions.Def_DepthOneQExp_spanProj
import Definitions.Def_DepthOneQExp_cnotAvg
import Theorems.Thm_DepthOneQExp_eq_2_43
import Theorems.Thm_DepthOneQExp_eq_2_51_2_52

open DepthOneQExp Matrix
open scoped Matrix.Norms.L2Operator Kronecker

namespace DepthOneQExp.Eq245Aux

variable {n : ℕ}

abbrev κ (n : ℕ) := MITMSynthesis.Q n × MITMSynthesis.Q n

theorem scalar_ineq (r : ℝ) (hr : 0 < r) (hr4 : r ^ 2 ≤ 1 / 4) (N : ℂ) (hN : N = ((r : ℂ) ^ 2)⁻¹)
    (α : Fin 5 → ℂ)
    (hc : ((!![N, 1, 1, (r : ℂ), (r : ℂ); 1, 1, (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      1, (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ); (r : ℂ), (r : ℂ), (r : ℂ), 1, (r : ℂ) ^ 2;
      (r : ℂ), (r : ℂ), (r : ℂ), (r : ℂ) ^ 2, 1] : Matrix (Fin 5) (Fin 5) ℂ) *ᵥ α) 0 = 0) :
    |(star α ⬝ᵥ ((!![2 * N, 2, 2, 2 * (r : ℂ), 2 * (r : ℂ); 2, 1, 2 * (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      2, 2 * (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ);
      2 * (r : ℂ), (r : ℂ), (r : ℂ), 0, 2 * (r : ℂ) ^ 2; 2 * (r : ℂ), (r : ℂ), (r : ℂ), 2 * (r : ℂ) ^ 2, 0] :
        Matrix (Fin 5) (Fin 5) ℂ) *ᵥ α)).re| ≤
      (1 - 2 * r ^ 2) / (1 - r ^ 2) *
        (star α ⬝ᵥ ((!![N, 1, 1, (r : ℂ), (r : ℂ); 1, 1, (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      1, (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ); (r : ℂ), (r : ℂ), (r : ℂ), 1, (r : ℂ) ^ 2;
      (r : ℂ), (r : ℂ), (r : ℂ), (r : ℂ) ^ 2, 1] : Matrix (Fin 5) (Fin 5) ℂ) *ᵥ α)).re := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [mulVec, dotProduct, Fin.sum_univ_five, Pi.star_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, empty_val',
    cons_val_fin_one, head_cons, tail_cons, Fin.isValue] at hc ⊢
  simp only [vecHead] at ⊢
  have e0 : α 0 = -(α 1 + α 2 + r * α 3 + r * α 4) * (r : ℂ) ^ 2 := by
    subst hN
    have : ((r : ℂ) ^ 2)⁻¹ * (r : ℂ) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero _ hr0)
    linear_combination (r : ℂ) ^ 2 * hc - α 0 * this
  have s0 : star (α 0) = -(star (α 1) + star (α 2) + r * star (α 3) + r * star (α 4)) * (r : ℂ) ^ 2 := by
    rw [e0]; simp [star_add, star_mul', Complex.conj_ofReal]
  obtain ⟨c1, hc1d⟩ : ∃ c, c = α 1 + r * (α 3 + α 4) := ⟨_, rfl⟩
  obtain ⟨c2, hc2d⟩ : ∃ c, c = α 2 + r * (α 3 + α 4) := ⟨_, rfl⟩
  obtain ⟨c3, hc3d⟩ : ∃ c, c = (α 3 + α 4) / 2 := ⟨_, rfl⟩
  obtain ⟨c4, hc4d⟩ : ∃ c, c = (α 3 - α 4) / 2 := ⟨_, rfl⟩
  have hc1 : star c1 * c1 = (Complex.normSq c1 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hc2 : star c2 * c2 = (Complex.normSq c2 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hc3 : star c3 * c3 = (Complex.normSq c3 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hc4 : star c4 * c4 = (Complex.normSq c4 : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have sc1 : star c1 = star (α 1) + r * (star (α 3) + star (α 4)) := by
    simp [hc1d, star_add, star_mul', Complex.conj_ofReal]
  have sc2 : star c2 = star (α 2) + r * (star (α 3) + star (α 4)) := by
    simp [hc2d, star_add, star_mul', Complex.conj_ofReal]
  have sc3 : star c3 = (star (α 3) + star (α 4)) / 2 := by
    simp [hc3d, star_add, star_div₀]
  have sc4 : star c4 = (star (α 3) - star (α 4)) / 2 := by
    simp [hc4d, star_sub, star_div₀]
  have hn1 := Complex.normSq_nonneg c1
  have hn2 := Complex.normSq_nonneg c2
  have hn3 := Complex.normSq_nonneg c3
  have hn4 := Complex.normSq_nonneg c4
  have key : ∀ zA zB : ℂ,
      zA = ((1 - 2 * r ^ 2) * (Complex.normSq c1 + Complex.normSq c2) -
        4 * r ^ 2 * (1 - 2 * r ^ 2) * Complex.normSq c3 - 4 * r ^ 2 * Complex.normSq c4 : ℝ) →
      zB = ((1 - r ^ 2) * (Complex.normSq c1 + Complex.normSq c2) +
        2 * (1 - r ^ 2) * (1 - 2 * r ^ 2) * Complex.normSq c3 + 2 * (1 - r ^ 2) * Complex.normSq c4 : ℝ) →
      |zA.re| ≤ (1 - 2 * r ^ 2) / (1 - r ^ 2) * zB.re := by
    rintro zA zB rfl rfl
    simp only [Complex.ofReal_re]
    have h1 : (0 : ℝ) < 1 - r ^ 2 := by linarith
    have e : (1 - 2 * r ^ 2) / (1 - r ^ 2) * ((1 - r ^ 2) * (Complex.normSq c1 + Complex.normSq c2) +
        2 * (1 - r ^ 2) * (1 - 2 * r ^ 2) * Complex.normSq c3 + 2 * (1 - r ^ 2) * Complex.normSq c4) =
        (1 - 2 * r ^ 2) * (Complex.normSq c1 + Complex.normSq c2) +
        2 * (1 - 2 * r ^ 2) ^ 2 * Complex.normSq c3 + 2 * (1 - 2 * r ^ 2) * Complex.normSq c4 := by
      field_simp
    rw [e, abs_le]
    have t1 : 0 ≤ 1 - 2 * r ^ 2 := by linarith
    have t2 : 0 ≤ 1 - 4 * r ^ 2 := by linarith
    constructor
    · nlinarith [mul_nonneg t1 hn1, mul_nonneg t1 hn2, mul_nonneg (mul_nonneg t1 t2) hn3,
        mul_nonneg t2 hn4]
    · nlinarith [mul_nonneg t1 hn3, hn4]
  apply key
  · rw [s0, e0]
    push_cast
    rw [← hc1, ← hc2, ← hc3, ← hc4, sc1, sc2, sc3, sc4, hc1d, hc2d, hc3d, hc4d]
    subst hN
    field_simp
    ring
  · rw [s0, e0]
    push_cast
    rw [← hc1, ← hc2, ← hc3, ← hc4, sc1, sc2, sc3, sc4, hc1d, hc2d, hc3d, hc4d]
    subst hN
    field_simp
    ring


theorem kron_perm {α : Type} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permToMatrix σ ⊗ₖ permToMatrix τ = permToMatrix (Equiv.prodCongr σ τ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, permToMatrix, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h1 : a = σ c <;> by_cases h2 : b = τ d <;> simp [h1, h2]

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

noncomputable def phi (n : ℕ) : Matrix (κ n) (κ n) ℂ :=
  (1 / (2 ^ n : ℂ)) • vecMulVec (maxEnt n) (star (maxEnt n))

theorem maxEnt_dot : star (maxEnt n) ⬝ᵥ maxEnt n = 2 ^ n := by
  simp only [dotProduct, maxEnt, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq, MITMSynthesis.Q]

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
  simp

noncomputable def Wm (σ : Equiv.Perm (MITMSynthesis.Q n)) : Matrix (κ n) (κ n) ℂ :=
  permToMatrix (Equiv.prodCongr σ σ)

theorem Wm_conjTranspose (σ : Equiv.Perm (MITMSynthesis.Q n)) : (Wm σ)ᴴ = Wm σ⁻¹ := by
  rw [Wm, permToMatrix_conjTranspose]; rfl

theorem Wm_mul (σ τ : Equiv.Perm (MITMSynthesis.Q n)) : Wm σ * Wm τ = Wm (σ * τ) := by
  rw [Wm, Wm, ← permToMatrix_mul]; rfl

theorem phi_mul_Wm (σ : Equiv.Perm (MITMSynthesis.Q n)) : phi n * Wm σ = phi n := by
  apply phi_mul
  rw [Wm_conjTranspose]
  exact perm_mulVec_maxEnt σ⁻¹

theorem cnotAvg_eq : cnotAvg n = (1 / (Fintype.card (cnotGroup n) : ℂ)) •
    ∑ g : cnotGroup n, Wm (g : Equiv.Perm (MITMSynthesis.Q n)) := by
  simp only [cnotAvg, Wm, kron_perm]

theorem card_ne : (Fintype.card (cnotGroup n) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_pos.ne'

theorem Wm_mul_cnotAvg (h : cnotGroup n) :
    Wm (h : Equiv.Perm (MITMSynthesis.Q n)) * cnotAvg n = cnotAvg n := by
  rw [cnotAvg_eq, Matrix.mul_smul, Finset.mul_sum]
  congr 1
  simp_rw [Wm_mul]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : cnotGroup n => Wm (g : Equiv.Perm (MITMSynthesis.Q n)))

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

theorem phi_mul_cnotAvg : phi n * cnotAvg n = phi n := by
  rw [cnotAvg_eq, Matrix.mul_smul, Finset.mul_sum]
  simp_rw [phi_mul_Wm]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem cnotAvg_mul_phi : cnotAvg n * phi n = phi n := by
  have := congrArg conjTranspose (phi_mul_cnotAvg (n := n))
  rwa [conjTranspose_mul, cnotAvg_herm, phi_herm] at this

theorem proj_norm_le {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℂ) (h1 : Qᴴ = Q)
    (h2 : Q * Q = Q) : ‖Q‖ ≤ 1 := by
  have := CStarRing.norm_star_mul_self (x := Q)
  rw [star_eq_conjTranspose, h1, h2] at this
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg Q]

/-! ### `Π` -/

theorem piProj_eq : piProj n = cnotAvg n - phi n := rfl

theorem piProj_herm : (piProj n)ᴴ = piProj n := by
  rw [piProj_eq, conjTranspose_sub, cnotAvg_herm, phi_herm]

theorem piProj_idem : piProj n * piProj n = piProj n := by
  rw [piProj_eq, sub_mul, mul_sub, mul_sub, cnotAvg_idem, cnotAvg_mul_phi, phi_mul_cnotAvg,
    phi_mul_phi]; abel

theorem phi_mul_piProj : phi n * piProj n = 0 := by
  rw [piProj_eq, mul_sub, phi_mul_cnotAvg, phi_mul_phi, sub_self]

/-! ### `H` -/

theorem xPerm_inv : (xPerm n 0)⁻¹ = xPerm n 0 := by
  rw [inv_eq_iff_mul_eq_one]
  refine Equiv.ext fun x => funext fun k => ?_
  show (xPerm n 0) ((xPerm n 0) x) k = x k
  have hX : ∀ y : MITMSynthesis.Q n,
      xPerm n 0 y = fun (k : Fin n) => if (k : ℕ) = 0 % n then y k + 1 else y k := fun _ => rfl
  rw [hX, hX]
  dsimp only
  split_ifs
  · generalize x k = c; revert c; decide
  · rfl

theorem zMat_herm : (zMat n 0)ᴴ = zMat n 0 := by
  rw [zMat, diagonal_conjTranspose]
  congr 1; funext x
  by_cases h : bit x 0 = 1 <;> simp [h]

theorem hOp_herm : (hOp n)ᴴ = hOp n := by
  rw [hOp, conjTranspose_add, conjTranspose_kronecker, conjTranspose_kronecker,
    permToMatrix_conjTranspose, xPerm_inv, zMat_herm]


/-! ### vectors -/

noncomputable def MM (n : ℕ) : Matrix (κ n) (Fin 5) ℂ := Matrix.of fun p i => aVec n i p

abbrev K (n : ℕ) : Submodule ℂ (EuclideanSpace ℂ (κ n)) :=
  Submodule.span ℂ (Set.range fun i : Fin 5 => WithLp.toLp 2 (aVec n i))

theorem toE_spanProj :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (spanProj n) = (K n).starProjection := by
  simp [spanProj]

theorem spanProj_mulVec (u : κ n → ℂ) :
    WithLp.toLp 2 (spanProj n *ᵥ u) = (K n).starProjection (WithLp.toLp 2 u) := by
  rw [← toE_spanProj]; rfl

theorem phi_mulVec (x : κ n → ℂ) :
    phi n *ᵥ x = ((1 / 2 ^ n : ℂ) * (star (maxEnt n) ⬝ᵥ x)) • maxEnt n := by
  funext p
  rw [phi, smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, vecMulVec, of_apply]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun q _ => by ring

theorem mem_K_piProj (hn : 2 ≤ n) (x : κ n → ℂ) : WithLp.toLp 2 (piProj n *ᵥ x) ∈ K n := by
  rw [piProj_eq, sub_mulVec, eq_2_43 n hn, WithLp.toLp_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · rw [spanProj_mulVec]; exact Submodule.starProjection_apply_mem _ _
  · rw [phi_mulVec, WithLp.toLp_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨0, rfl⟩

theorem MM_mulVec (α : Fin 5 → ℂ) : MM n *ᵥ α = ∑ i, α i • aVec n i := by
  funext p
  simp [MM, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem mem_K_MM (α : Fin 5 → ℂ) : WithLp.toLp 2 (MM n *ᵥ α) ∈ K n := by
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨α, ?_⟩
  rw [MM_mulVec]
  simp only [← WithLp.toLp_smul, ← WithLp.toLp_sum]

theorem exists_alpha (u : κ n → ℂ) (hu : WithLp.toLp 2 u ∈ K n) : ∃ α, u = MM n *ᵥ α := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hu
  refine ⟨c, ?_⟩
  rw [MM_mulVec]
  have := congrArg WithLp.ofLp hc
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at this
  exact this.symm

theorem maxEnt_piProj (x : κ n → ℂ) : star (maxEnt n) ⬝ᵥ (piProj n *ᵥ x) = 0 := by
  have h := congrArg (fun A => A *ᵥ x) (phi_mul_piProj (n := n))
  simp only [← mulVec_mulVec, zero_mulVec] at h
  rw [phi_mulVec] at h
  have := congrFun h (0, 0)
  simp only [Pi.smul_apply, maxEnt, if_true, smul_eq_mul, mul_one, Pi.zero_apply] at this
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  rcases mul_eq_zero.1 this with h3 | h3
  · simp at h3
  · exact h3

theorem quadH (α : Fin 5 → ℂ) : star (MM n *ᵥ α) ⬝ᵥ (hOp n *ᵥ (MM n *ᵥ α)) =
    star α ⬝ᵥ (((MM n)ᴴ * hOp n * MM n) *ᵥ α) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem quad1 (α : Fin 5 → ℂ) : star (MM n *ᵥ α) ⬝ᵥ (MM n *ᵥ α) =
    star α ⬝ᵥ (((MM n)ᴴ * MM n) *ᵥ α) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem constraint (α : Fin 5 → ℂ) :
    (((MM n)ᴴ * MM n) *ᵥ α) 0 = star (maxEnt n) ⬝ᵥ (MM n *ᵥ α) := by
  rw [← mulVec_mulVec]
  simp only [mulVec, dotProduct, conjTranspose_apply, Pi.star_apply]
  rfl

noncomputable def rR (n : ℕ) : ℝ := (Real.sqrt (2 ^ n))⁻¹

theorem rR_pos : 0 < rR n := by
  unfold rR; positivity

theorem rR_sq : rR n ^ 2 = 1 / 2 ^ n := by
  rw [rR, inv_pow, Real.sq_sqrt (by positivity), one_div]

theorem two_pow_eqC : (2 : ℂ) ^ n = (((rR n : ℝ) : ℂ) ^ 2)⁻¹ := by
  rw [← Complex.ofReal_pow, rR_sq]
  simp

theorem lam_eq : ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) = (1 - 2 * rR n ^ 2) / (1 - rR n ^ 2) := by
  rw [rR_sq]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

theorem rR_sq_le (hn : 2 ≤ n) : rR n ^ 2 ≤ 1 / 4 := by
  rw [rR_sq]
  have : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  exact one_div_le_one_div_of_le (by norm_num) this

theorem core (hn : 2 ≤ n) (u : κ n → ℂ) (hu : WithLp.toLp 2 u ∈ K n)
    (h0 : star (maxEnt n) ⬝ᵥ u = 0) :
    |(star u ⬝ᵥ (hOp n *ᵥ u)).re| ≤
      ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) * (star u ⬝ᵥ u).re := by
  obtain ⟨α, rfl⟩ := exists_alpha u hu
  have g1 : (MM n)ᴴ * MM n = _ := (eq_2_51_2_52 n hn).1
  have g2 : (MM n)ᴴ * hOp n * MM n = _ := (eq_2_51_2_52 n hn).2.1
  have hc := constraint (n := n) α
  rw [h0, g1] at hc
  rw [quadH, quad1, g1, g2, lam_eq]
  exact scalar_ineq (rR n) rR_pos (rR_sq_le hn) _ two_pow_eqC α hc


theorem val1 (r : ℝ) (hr : r ≠ 0) (N : ℂ) (hN : N = ((r : ℂ) ^ 2)⁻¹) :
    ((!![N, 1, 1, (r : ℂ), (r : ℂ); 1, 1, (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      1, (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ); (r : ℂ), (r : ℂ), (r : ℂ), 1, (r : ℂ) ^ 2;
      (r : ℂ), (r : ℂ), (r : ℂ), (r : ℂ) ^ 2, 1] : Matrix (Fin 5) (Fin 5) ℂ) *ᵥ ![-(r : ℂ) ^ 2, 1, 0, 0, 0]) 0 = 0 := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [mulVec, dotProduct, Fin.sum_univ_five, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, empty_val',
    cons_val_fin_one, head_cons, tail_cons, Fin.isValue]
  try simp only [vecHead]
  subst hN
  field_simp
  ring

theorem val2 (r : ℝ) (hr : r ≠ 0) (N : ℂ) (hN : N = ((r : ℂ) ^ 2)⁻¹) :
    star ![-(r : ℂ) ^ 2, 1, 0, 0, 0] ⬝ᵥ ((!![2 * N, 2, 2, 2 * (r : ℂ), 2 * (r : ℂ); 2, 1, 2 * (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      2, 2 * (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ);
      2 * (r : ℂ), (r : ℂ), (r : ℂ), 0, 2 * (r : ℂ) ^ 2; 2 * (r : ℂ), (r : ℂ), (r : ℂ), 2 * (r : ℂ) ^ 2, 0] :
        Matrix (Fin 5) (Fin 5) ℂ) *ᵥ ![-(r : ℂ) ^ 2, 1, 0, 0, 0]) =
      ((1 - 2 * r ^ 2 : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [mulVec, dotProduct, Fin.sum_univ_five, Pi.star_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, empty_val',
    cons_val_fin_one, head_cons, tail_cons, Fin.isValue]
  try simp only [vecHead]
  simp only [star_neg, star_pow, Complex.star_def, Complex.conj_ofReal, star_one, star_zero]
  subst hN
  push_cast
  field_simp
  ring

theorem val3 (r : ℝ) (hr : r ≠ 0) (N : ℂ) (hN : N = ((r : ℂ) ^ 2)⁻¹) :
    star ![-(r : ℂ) ^ 2, 1, 0, 0, 0] ⬝ᵥ ((!![N, 1, 1, (r : ℂ), (r : ℂ); 1, 1, (r : ℂ) ^ 2, (r : ℂ), (r : ℂ);
      1, (r : ℂ) ^ 2, 1, (r : ℂ), (r : ℂ); (r : ℂ), (r : ℂ), (r : ℂ), 1, (r : ℂ) ^ 2;
      (r : ℂ), (r : ℂ), (r : ℂ), (r : ℂ) ^ 2, 1] : Matrix (Fin 5) (Fin 5) ℂ) *ᵥ ![-(r : ℂ) ^ 2, 1, 0, 0, 0]) =
      ((1 - r ^ 2 : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [mulVec, dotProduct, Fin.sum_univ_five, Pi.star_apply, of_apply, cons_val',
    cons_val_zero, cons_val_one, cons_val_two, cons_val_three, cons_val_four, empty_val',
    cons_val_fin_one, head_cons, tail_cons, Fin.isValue]
  try simp only [vecHead]
  simp only [star_neg, star_pow, Complex.star_def, Complex.conj_ofReal, star_one, star_zero]
  subst hN
  push_cast
  field_simp
  ring

theorem T_herm : (piProj n * hOp n * piProj n)ᴴ = piProj n * hOp n * piProj n := by
  rw [conjTranspose_mul, conjTranspose_mul, piProj_herm, hOp_herm, Matrix.mul_assoc]

theorem inner_T (x : κ n → ℂ) :
    inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (piProj n * hOp n * piProj n)
      (WithLp.toLp 2 x)) (WithLp.toLp 2 x) =
    star (piProj n *ᵥ x) ⬝ᵥ (hOp n *ᵥ (piProj n *ᵥ x)) := by
  rw [toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, star_mulVec, dotProduct_comm,
    ← dotProduct_mulVec, T_herm, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
  rw [show star x ᵥ* piProj n = star (piProj n *ᵥ x) by rw [star_mulVec, piProj_herm]]

theorem norm_sq_toLp (v : κ n → ℂ) : ‖WithLp.toLp 2 v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rfl

theorem piProj_norm_le : ‖piProj n‖ ≤ 1 := proj_norm_le _ piProj_herm piProj_idem

theorem toLp_piProj_norm (x : κ n → ℂ) :
    ‖WithLp.toLp 2 (piProj n *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  have := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (piProj n)).le_opNorm (WithLp.toLp 2 x)
  rw [toEuclideanCLM_toLp] at this
  refine this.trans ?_
  have h1 : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (piProj n)‖ ≤ 1 := piProj_norm_le
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

theorem upper (hn : 2 ≤ n) (x : κ n → ℂ) :
    |(inner ℂ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (piProj n * hOp n * piProj n)
      (WithLp.toLp 2 x)) (WithLp.toLp 2 x)).re| ≤
      ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [inner_T]
  have hc := core hn (piProj n *ᵥ x) (mem_K_piProj hn x) (maxEnt_piProj x)
  refine hc.trans ?_
  rw [← norm_sq_toLp]
  have h4 : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hl : 0 ≤ ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) := div_nonneg (by linarith) (by linarith)
  apply mul_le_mul_of_nonneg_left _ hl
  have := toLp_piProj_norm x
  exact pow_le_pow_left₀ (norm_nonneg _) this 2


theorem lower (hn : 2 ≤ n) : ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) ≤
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (piProj n * hOp n * piProj n)‖ := by
  set α : Fin 5 → ℂ := ![-((rR n : ℝ) : ℂ) ^ 2, 1, 0, 0, 0] with hα
  set v := MM n *ᵥ α with hv
  have g1 : (MM n)ᴴ * MM n = _ := (eq_2_51_2_52 n hn).1
  have g2 : (MM n)ᴴ * hOp n * MM n = _ := (eq_2_51_2_52 n hn).2.1
  have hr : rR n ≠ 0 := rR_pos.ne'
  have hv0 : star (maxEnt n) ⬝ᵥ v = 0 := by
    rw [hv, ← constraint, g1]
    exact val1 (rR n) hr _ two_pow_eqC
  have hPv : piProj n *ᵥ v = v := by
    rw [piProj_eq, sub_mulVec, eq_2_43 n hn, phi_mulVec, hv0, mul_zero, zero_smul, sub_zero]
    apply WithLp.toLp_injective 2
    rw [spanProj_mulVec, Submodule.starProjection_eq_self_iff.2 (mem_K_MM α)]
  have hA : star v ⬝ᵥ (hOp n *ᵥ v) = ((1 - 2 * rR n ^ 2 : ℝ) : ℂ) := by
    rw [hv, quadH, g2]
    exact val2 (rR n) hr _ two_pow_eqC
  have hB : ‖WithLp.toLp 2 v‖ ^ 2 = 1 - rR n ^ 2 := by
    rw [norm_sq_toLp, hv, quad1, g1]
    exact (congrArg Complex.re (val3 (rR n) hr _ two_pow_eqC)).trans (Complex.ofReal_re _)
  have key := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n)
    (piProj n * hOp n * piProj n)).rayleighQuotient_le_norm (WithLp.toLp 2 v)
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_T, hPv, hA, hB] at key
  simp only [RCLike.re_to_complex, Complex.ofReal_re] at key
  rw [lam_eq]
  exact (le_abs_self _).trans key

end DepthOneQExp.Eq245Aux

open DepthOneQExp.Eq245Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    ‖piProj n * hOp n * piProj n‖ = ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) := by
  set T := piProj n * hOp n * piProj n with hT
  set Tc := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) T with hTc
  have hnorm : ‖T‖ = ‖Tc‖ := rfl
  have h4 : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hl : 0 ≤ ((2 : ℝ) ^ n - 2) / ((2 : ℝ) ^ n - 1) := div_nonneg (by linarith) (by linarith)
  have hsym : (Tc : EuclideanSpace ℂ (κ n) →ₗ[ℂ] EuclideanSpace ℂ (κ n)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr T_herm
  rw [hnorm]
  apply le_antisymm
  · rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient Tc hsym]
    apply ciSup_le
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, y = WithLp.toLp 2 x := ⟨WithLp.ofLp y, rfl⟩
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖WithLp.toLp 2 x‖ ^ 2)]
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ ‖WithLp.toLp 2 x‖ ^ 2) with h0 | h0
    · rw [← h0, div_zero]; exact hl
    · rw [div_le_iff₀ h0]
      exact upper hn x
  · exact lower hn
