-- Prove2me | solution 1 for DepthOneQExp.relT_gem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:41:04.579866+00:00
-- url     : https://prove2.me/submissions/93283385-b992-4f0b-8507-bd075ac8a53e

import Mathlib
import Definitions.Def_DepthOneQExp_kassabovA
import Definitions.Def_DepthOneQExp_kassabovB
import Definitions.Def_DepthOneQExp_blockElem
import Definitions.Def_DepthOneQExp_sigma
import Definitions.Def_ConstGapCircuits_spectralGap

set_option linter.unusedSectionVars false


open scoped InnerProductSpace


namespace KasF

variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- a unitary representation of a finite abelian group by operators -/
structure URep (A V : Type) [AddCommGroup A] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] where
  W : A → (V →L[ℂ] V)
  map_zero : W 0 = 1
  map_add : ∀ a b, W (a + b) = W a * W b
  adj : ∀ a, ContinuousLinearMap.adjoint (W a) = W (-a)

variable (ρ : URep A V)

/-- spectral projection for the character `ψ` -/
noncomputable def proj (ψ : AddChar A ℂ) : V →L[ℂ] V :=
  (1 / (Fintype.card A : ℂ)) • ∑ a, ψ (-a) • ρ.W a

theorem card_ne : (Fintype.card A : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero

theorem sum_W_shift (b : A) (ψ : AddChar A ℂ) :
    ∑ a, ψ (-a) • ρ.W (b + a) = ψ b • ∑ a, ψ (-a) • ρ.W a := by
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft b) _ _ fun a => ?_
  simp only [Equiv.coe_addLeft, smul_smul]
  congr 1
  rw [← AddChar.map_add_eq_mul]
  congr 1; abel

theorem W_mul_proj (b : A) (ψ : AddChar A ℂ) : ρ.W b * proj ρ ψ = ψ b • proj ρ ψ := by
  unfold proj
  rw [mul_smul_comm, smul_comm (ψ b)]
  congr 1
  rw [Finset.mul_sum]
  simp_rw [mul_smul_comm, ← ρ.map_add]
  exact sum_W_shift ρ b ψ

theorem proj_mul_W (b : A) (ψ : AddChar A ℂ) : proj ρ ψ * ρ.W b = ψ b • proj ρ ψ := by
  unfold proj
  rw [smul_mul_assoc, smul_comm (ψ b)]
  congr 1
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, ← ρ.map_add, add_comm _ b]
  exact sum_W_shift ρ b ψ

theorem orth_sum (ψ φ : AddChar A ℂ) :
    ∑ a, ψ (-a) * φ a = if ψ = φ then (Fintype.card A : ℂ) else 0 := by
  have h := AddChar.sum_eq_ite (ψ⁻¹ * φ)
  simp only [AddChar.mul_apply, AddChar.inv_apply] at h
  rw [h]
  congr 1
  rw [← AddChar.one_eq_zero]
  exact propext inv_mul_eq_one

theorem proj_mul_proj (ψ φ : AddChar A ℂ) :
    proj ρ ψ * proj ρ φ = if ψ = φ then proj ρ ψ else 0 := by
  conv_lhs => rw [proj]
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [smul_mul_assoc, W_mul_proj, smul_smul, ← Finset.sum_smul, orth_sum]
  split_ifs with h
  · subst h; rw [one_div, smul_smul, inv_mul_cancel₀ card_ne, one_smul]
  · simp

theorem proj_adj (ψ : AddChar A ℂ) : ContinuousLinearMap.adjoint (proj ρ ψ) = proj ρ ψ := by
  unfold proj
  rw [LinearIsometryEquiv.map_smulₛₗ, map_sum]
  simp_rw [LinearIsometryEquiv.map_smulₛₗ, ρ.adj]
  congr 1
  · simp
  · refine Fintype.sum_equiv (Equiv.neg A) _ _ fun a => ?_
    simp only [Equiv.neg_apply, neg_neg]
    congr 1
    rw [AddChar.map_neg_eq_conj, RingHomCompTriple.comp_apply, RingHom.id_apply]

theorem sum_proj : ∑ ψ : AddChar A ℂ, proj ρ ψ = 1 := by
  unfold proj
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, AddChar.sum_apply_eq_ite, neg_eq_zero]
  rw [Finset.sum_eq_single 0]
  · simp [ρ.map_zero, smul_smul, inv_mul_cancel₀ card_ne]
  · intro b _ hb; simp [hb]
  · simp

theorem proj_inner (ψ φ : AddChar A ℂ) (w : V) :
    ⟪proj ρ ψ w, proj ρ φ w⟫_ℂ = if ψ = φ then ⟪proj ρ ψ w, proj ρ ψ w⟫_ℂ else 0 := by
  split_ifs with h
  · rw [h]
  · rw [← ContinuousLinearMap.adjoint_inner_right, proj_adj, ← ContinuousLinearMap.mul_apply,
      proj_mul_proj, if_neg h]
    simp

/-- Parseval for a family of coefficients over a finset of characters -/
theorem norm_sq_sum (S : Finset (AddChar A ℂ)) (c : AddChar A ℂ → ℂ) (w : V) :
    ‖∑ ψ ∈ S, c ψ • proj ρ ψ w‖ ^ 2 = ∑ ψ ∈ S, ‖c ψ‖ ^ 2 * ‖proj ρ ψ w‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  rw [inner_sum, Finset.sum_eq_single ψ]
  · rw [inner_smul_left, inner_smul_right, proj_inner, if_pos rfl, ← mul_assoc,
      mul_comm ((starRingEnd ℂ) (c ψ)), RCLike.mul_conj]
    rw [← RCLike.ofReal_pow, RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
  · intro φ _ hφ
    rw [inner_smul_left, inner_smul_right, proj_inner, if_neg (Ne.symm hφ)]; simp
  · intro h; exact absurd hψ h

theorem norm_sq_eq_sum (w : V) : ‖w‖ ^ 2 = ∑ ψ : AddChar A ℂ, ‖proj ρ ψ w‖ ^ 2 := by
  have h1 : w = ∑ ψ : AddChar A ℂ, (1 : ℂ) • proj ρ ψ w := by
    simp only [one_smul]
    rw [← ContinuousLinearMap.sum_apply, sum_proj, ContinuousLinearMap.one_apply]
  conv_lhs => rw [h1]
  rw [norm_sq_sum]
  simp

theorem W_sub_eq (a : A) (w : V) :
    ρ.W a w - w = ∑ ψ : AddChar A ℂ, (ψ a - 1) • proj ρ ψ w := by
  have h1 : ∀ u : V, u = ∑ ψ : AddChar A ℂ, proj ρ ψ u := by
    intro u
    rw [← ContinuousLinearMap.sum_apply, sum_proj, ContinuousLinearMap.one_apply]
  conv_lhs => rw [h1 w]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [← ContinuousLinearMap.mul_apply, W_mul_proj, sub_smul, one_smul,
    ContinuousLinearMap.smul_apply]

theorem W_sub_norm_sq (a : A) (w : V) :
    ‖ρ.W a w - w‖ ^ 2 = ∑ ψ : AddChar A ℂ, ‖ψ a - 1‖ ^ 2 * ‖proj ρ ψ w‖ ^ 2 := by
  rw [W_sub_eq, norm_sq_sum]

/-- transport of characters along an additive automorphism: `ψ ↦ ψ ∘ c⁻¹` -/
def charMap (c : A ≃+ A) : AddChar A ℂ ≃ AddChar A ℂ where
  toFun ψ := ψ.compAddMonoidHom c.symm.toAddMonoidHom
  invFun ψ := ψ.compAddMonoidHom c.toAddMonoidHom
  left_inv ψ := by ext a; simp
  right_inv ψ := by ext a; simp

theorem charMap_apply (c : A ≃+ A) (ψ : AddChar A ℂ) (a : A) : charMap c ψ a = ψ (c.symm a) := rfl

theorem conj_proj (g : V →L[ℂ] V) (c : A ≃+ A) (hc : ∀ a, g * ρ.W a = ρ.W (c a) * g)
    (ψ : AddChar A ℂ) : g * proj ρ ψ = proj ρ (charMap c ψ) * g := by
  unfold proj
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  simp_rw [mul_smul_comm, hc, smul_mul_assoc]
  refine Fintype.sum_equiv c.toEquiv _ _ fun a => ?_
  simp [charMap_apply, map_neg]

/-- the spectral "measure" of a finset of characters at a vector -/
noncomputable def mu (S : Finset (AddChar A ℂ)) (w : V) : ℝ := ∑ ψ ∈ S, ‖proj ρ ψ w‖ ^ 2

noncomputable def projS (S : Finset (AddChar A ℂ)) : V →L[ℂ] V := ∑ ψ ∈ S, proj ρ ψ

theorem mu_eq (S : Finset (AddChar A ℂ)) (w : V) : mu ρ S w = ‖projS ρ S w‖ ^ 2 := by
  have := norm_sq_sum ρ S (fun _ => 1) w
  simp only [one_smul, norm_one, one_pow, one_mul] at this
  rw [mu, projS, ContinuousLinearMap.sum_apply, this]

theorem mu_le (S : Finset (AddChar A ℂ)) (w : V) : mu ρ S w ≤ ‖w‖ ^ 2 := by
  rw [mu, norm_sq_eq_sum ρ w]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem sqrt_mu_eq (S : Finset (AddChar A ℂ)) (w : V) : Real.sqrt (mu ρ S w) = ‖projS ρ S w‖ := by
  rw [mu_eq, Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_mu_lip (S : Finset (AddChar A ℂ)) (w1 w2 : V) :
    Real.sqrt (mu ρ S w1) ≤ Real.sqrt (mu ρ S w2) + ‖w1 - w2‖ := by
  rw [sqrt_mu_eq, sqrt_mu_eq]
  have h1 : ‖projS ρ S w1‖ ≤ ‖projS ρ S w2‖ + ‖projS ρ S (w1 - w2)‖ := by
    rw [map_sub]
    have := norm_sub_norm_le (projS ρ S w1) (projS ρ S w2)
    linarith
  have h2 : ‖projS ρ S (w1 - w2)‖ ≤ ‖w1 - w2‖ := by
    rw [← sqrt_mu_eq]
    calc Real.sqrt (mu ρ S (w1 - w2)) ≤ Real.sqrt (‖w1 - w2‖ ^ 2) := Real.sqrt_le_sqrt (mu_le ρ S _)
      _ = ‖w1 - w2‖ := Real.sqrt_sq (norm_nonneg _)
  linarith

/-- the shift lemma (Kassabov, Lemma 2.4): if `g` is unitary and conjugates `W` through `c`, then
`√μ(c·S) ≤ √μ(S) + ‖g v - v‖`. -/
theorem shift (g : V →L[ℂ] V) (hg : ContinuousLinearMap.adjoint g * g = 1)
    (hg' : g * ContinuousLinearMap.adjoint g = 1) (c : A ≃+ A)
    (hc : ∀ a, g * ρ.W a = ρ.W (c a) * g) (S : Finset (AddChar A ℂ)) (v : V) :
    Real.sqrt (mu ρ (S.map (charMap c).toEmbedding) v) ≤ Real.sqrt (mu ρ S v) + ‖g v - v‖ := by
  set gs := ContinuousLinearMap.adjoint g
  have hiso : ∀ w, ‖g w‖ = ‖w‖ := by
    intro w
    have : ‖g w‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ),
        ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, hg,
        ContinuousLinearMap.one_apply]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hmu : mu ρ (S.map (charMap c).toEmbedding) v = mu ρ S (gs v) := by
    rw [mu, Finset.sum_map, mu]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    have : proj ρ (charMap c ψ) v = g (proj ρ ψ (gs v)) := by
      rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, conj_proj ρ g c hc,
        mul_assoc, hg', mul_one]
    simp only [Equiv.toEmbedding_apply]
    rw [this, hiso]
  rw [hmu]
  have h1 := sqrt_mu_lip ρ S (gs v) v
  have h2 : ‖gs v - v‖ = ‖g v - v‖ := by
    rw [← hiso (gs v - v), map_sub, ← ContinuousLinearMap.mul_apply, hg', ContinuousLinearMap.one_apply,
      norm_sub_rev]
  linarith

end KasF




namespace KasV

variable {R : Type} [Ring R] [Fintype R] [DecidableEq R]
variable (x : Fin 2 → R)

/-- the word-length filtration: `R₀ = ℤ·1`, `R_{n+1} = R₀ + Σᵢ xᵢ Rₙ` -/
def Rn : ℕ → AddSubgroup R
  | 0 => AddSubgroup.zmultiples 1
  | n + 1 => AddSubgroup.zmultiples 1 ⊔ (Rn n).map (AddMonoidHom.mulLeft (x 0)) ⊔
      (Rn n).map (AddMonoidHom.mulLeft (x 1))

theorem one_mem_Rn (n : ℕ) : (1 : R) ∈ Rn x n := by
  cases n with
  | zero => exact AddSubgroup.mem_zmultiples 1
  | succ n => exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_left (AddSubgroup.mem_zmultiples 1))

theorem R0_le (n : ℕ) : Rn x 0 ≤ Rn x n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_sup_left.trans le_sup_left

theorem mul_mem_Rn (n : ℕ) (i : Fin 2) (r : R) (hr : r ∈ Rn x n) : x i * r ∈ Rn x (n + 1) := by
  fin_cases i
  · exact AddSubgroup.mem_sup_left (AddSubgroup.mem_sup_right ⟨r, hr, rfl⟩)
  · exact AddSubgroup.mem_sup_right ⟨r, hr, rfl⟩

theorem Rn_mono_succ (n : ℕ) : Rn x n ≤ Rn x (n + 1) := by
  induction n with
  | zero => exact le_sup_left.trans le_sup_left
  | succ n ih =>
    show AddSubgroup.zmultiples 1 ⊔ (Rn x n).map (AddMonoidHom.mulLeft (x 0)) ⊔
      (Rn x n).map (AddMonoidHom.mulLeft (x 1)) ≤ AddSubgroup.zmultiples 1 ⊔
      (Rn x (n + 1)).map (AddMonoidHom.mulLeft (x 0)) ⊔ (Rn x (n + 1)).map (AddMonoidHom.mulLeft (x 1))
    exact sup_le_sup (sup_le_sup le_rfl (AddSubgroup.map_mono ih)) (AddSubgroup.map_mono ih)

theorem Rn_mono {m n : ℕ} (h : m ≤ n) : Rn x m ≤ Rn x n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Rn_mono_succ x _)

/-- `R_{n+1} = R₀ + x₀ Rₙ + x₁ Rₙ` as a membership statement -/
theorem mem_Rn_succ (n : ℕ) (r : R) (hr : r ∈ Rn x (n + 1)) :
    ∃ z ∈ Rn x 0, ∃ a ∈ Rn x n, ∃ b ∈ Rn x n, r = z + x 0 * a + x 1 * b := by
  obtain ⟨y, hy, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hr
  obtain ⟨z, hz, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hy
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hw
  exact ⟨z, hz, a, ha, b, hb, rfl⟩

section Val
variable {N : ℕ} (hN : Rn x N = ⊤)

open Classical in
/-- the valuation of a character: the least level of the filtration on which it is nontrivial
(`N + 1` stands for `∞`, i.e. the trivial character) -/
noncomputable def nu (N : ℕ) (ψ : AddChar R ℂ) : ℕ :=
  Nat.find (⟨N + 1, Or.inl rfl⟩ : ∃ n, n = N + 1 ∨ ∃ r ∈ Rn x n, ψ r ≠ 1)

theorem nu_le (ψ : AddChar R ℂ) : nu x N ψ ≤ N + 1 := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

theorem triv_of_lt (ψ : AddChar R ℂ) {m : ℕ} (hm : m < nu x N ψ) : ∀ r ∈ Rn x m, ψ r = 1 := by
  classical
  intro r hr
  by_contra h
  exact Nat.find_min _ hm (Or.inr ⟨r, hr, h⟩)

theorem nu_spec (ψ : AddChar R ℂ) (h : nu x N ψ ≤ N) : ∃ r ∈ Rn x (nu x N ψ), ψ r ≠ 1 := by
  classical
  rcases Nat.find_spec (⟨N + 1, Or.inl rfl⟩ : ∃ n, n = N + 1 ∨ ∃ r ∈ Rn x n, ψ r ≠ 1) with h1 | h1
  · exact absurd h (by unfold nu at *; omega)
  · exact h1

include hN in
theorem nu_le_N_of_ne (ψ : AddChar R ℂ) (hψ : ψ ≠ 1) : nu x N ψ ≤ N := by
  by_contra h
  apply hψ
  ext r
  exact triv_of_lt (N := N) x ψ (show N < nu x N ψ by omega) r (by rw [hN]; trivial)

include hN in
theorem nu_eq_top_iff (ψ : AddChar R ℂ) : nu x N ψ = N + 1 ↔ ψ = 1 := by
  constructor
  · intro h
    by_contra hψ
    have := nu_le_N_of_ne x hN ψ hψ
    omega
  · rintro rfl
    apply le_antisymm (nu_le (N := N) x _)
    by_contra h
    push Not at h
    obtain ⟨r, _, hr⟩ := nu_spec (N := N) x (1 : AddChar R ℂ) (by omega)
    exact hr rfl

theorem le_nu_of_triv (ψ : AddChar R ℂ) (n : ℕ) (hn : n ≤ N + 1)
    (h : ∀ m < n, ∀ r ∈ Rn x m, ψ r = 1) : n ≤ nu x N ψ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr, hψ⟩ := nu_spec (N := N) x ψ (by omega)
  exact hψ (h _ hlt r hr)

theorem nu_le_of_nontriv (ψ : AddChar R ℂ) (n : ℕ) (r : R) (hr : r ∈ Rn x n) (hψ : ψ r ≠ 1) :
    nu x N ψ ≤ n := by
  by_contra h
  push Not at h
  exact hψ (triv_of_lt (N := N) x ψ h r hr)

/-- (a) `ν ψ = 0 ↔ ψ 1 ≠ 1` -/
theorem nu_eq_zero_iff (ψ : AddChar R ℂ) : nu x N ψ = 0 ↔ ψ 1 ≠ 1 := by
  constructor
  · intro h
    obtain ⟨r, hr, hψ⟩ := nu_spec (N := N) x ψ (by omega)
    rw [h] at hr
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hr
    intro h1; apply hψ
    rw [AddChar.map_zsmul_eq_zpow, h1, one_zpow]
  · intro h
    have := nu_le_of_nontriv (N := N) x ψ 0 1 (AddSubgroup.mem_zmultiples 1) h
    omega

/-- (b) `ν ψ < ν φ → ν (ψ φ) = ν ψ` -/
theorem nu_mul (ψ φ : AddChar R ℂ) (h : nu x N ψ < nu x N φ) : nu x N (ψ * φ) = nu x N ψ := by
  apply le_antisymm
  · obtain ⟨r, hr, hψ⟩ := nu_spec (N := N) x ψ (by have := nu_le (N := N) x φ; omega)
    refine nu_le_of_nontriv (N := N) x _ _ r hr ?_
    rw [AddChar.mul_apply, triv_of_lt (N := N) x φ h r hr, mul_one]; exact hψ
  · refine le_nu_of_triv (N := N) x _ _ (nu_le (N := N) x ψ) fun m hm r hr => ?_
    rw [AddChar.mul_apply, triv_of_lt (N := N) x ψ hm r hr, triv_of_lt (N := N) x φ (by omega) r hr, mul_one]

/-- left translate of a character -/
noncomputable def lt (r : R) (ψ : AddChar R ℂ) : AddChar R ℂ := ψ.compAddMonoidHom (AddMonoidHom.mulLeft r)

theorem lt_apply (r : R) (ψ : AddChar R ℂ) (a : R) : lt r ψ a = ψ (r * a) := rfl

/-- (d) -/
theorem nu_lt_ge (ψ : AddChar R ℂ) (i : Fin 2) : nu x N ψ - 1 ≤ nu x N (lt (x i) ψ) := by
  refine le_nu_of_triv (N := N) x _ _ (by have := nu_le (N := N) x ψ; omega) fun m hm r hr => ?_
  rw [lt_apply]
  exact triv_of_lt (N := N) x ψ (by omega) _ (mul_mem_Rn x m i r hr)

include hN in
/-- (c) -/
theorem nu_lt_exists (ψ : AddChar R ℂ) (h0 : 0 < nu x N ψ) (hN' : nu x N ψ ≤ N) :
    ∃ i, nu x N (lt (x i) ψ) = nu x N ψ - 1 := by
  obtain ⟨r, hr, hψ⟩ := nu_spec (N := N) x ψ hN'
  obtain ⟨n, hn⟩ : ∃ n, nu x N ψ = n + 1 := ⟨nu x N ψ - 1, by omega⟩
  rw [hn] at hr
  obtain ⟨z, hz, a, ha, b, hb, rfl⟩ := mem_Rn_succ x n r hr
  have hz1 : ψ z = 1 := triv_of_lt (N := N) x ψ (by omega) z ((R0_le x n) hz)
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hz1, one_mul] at hψ
  by_cases h0' : ψ (x 0 * a) = 1
  · rw [h0', one_mul] at hψ
    refine ⟨1, le_antisymm ?_ (nu_lt_ge (N := N) x ψ 1)⟩
    rw [hn, Nat.add_sub_cancel]
    exact nu_le_of_nontriv (N := N) x _ n b hb (by rw [lt_apply]; exact hψ)
  · refine ⟨0, le_antisymm ?_ (nu_lt_ge (N := N) x ψ 0)⟩
    rw [hn, Nat.add_sub_cancel]
    exact nu_le_of_nontriv (N := N) x _ n a ha (by rw [lt_apply]; exact h0')

end Val

end KasV



open scoped InnerProductSpace
open KasF KasV

namespace KasA

variable {R : Type} [Ring R] [Fintype R] [DecidableEq R]

/-- `(a₁, a₂) ↦ (a₁ + r a₂, a₂)` -/
def cu (h2 : ∀ r : R, r + r = 0) (r : R) : (R × R) ≃+ (R × R) where
  toFun a := (a.1 + r * a.2, a.2)
  invFun a := (a.1 + r * a.2, a.2)
  left_inv a := by ext <;> simp [add_assoc, h2]
  right_inv a := by ext <;> simp [add_assoc, h2]
  map_add' a b := by ext <;> simp [mul_add] <;> abel

/-- `(a₁, a₂) ↦ (a₁, a₂ + r a₁)` -/
def cl (h2 : ∀ r : R, r + r = 0) (r : R) : (R × R) ≃+ (R × R) where
  toFun a := (a.1, a.2 + r * a.1)
  invFun a := (a.1, a.2 + r * a.1)
  left_inv a := by ext <;> simp [add_assoc, h2]
  right_inv a := by ext <;> simp [add_assoc, h2]
  map_add' a b := by ext <;> simp [mul_add] <;> abel

/-- the two components of a character of `R × R` -/
noncomputable def c1 (ψ : AddChar (R × R) ℂ) : AddChar R ℂ := ψ.compAddMonoidHom (AddMonoidHom.inl R R)
noncomputable def c2 (ψ : AddChar (R × R) ℂ) : AddChar R ℂ := ψ.compAddMonoidHom (AddMonoidHom.inr R R)

theorem char_split (ψ : AddChar (R × R) ℂ) (a : R × R) : ψ a = c1 ψ a.1 * c2 ψ a.2 := by
  show ψ a = ψ (a.1, 0) * ψ (0, a.2)
  rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp

theorem char_eq_one_iff (ψ : AddChar (R × R) ℂ) : ψ = 1 ↔ c1 ψ = 1 ∧ c2 ψ = 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; ext a; rw [char_split, h1, h2]; simp

theorem c1_charMap_cu (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    c1 (charMap (cu h2 r) ψ) = c1 ψ := by
  ext a; simp [c1, charMap_apply, cu]

theorem c2_charMap_cu (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    c2 (charMap (cu h2 r) ψ) = lt r (c1 ψ) * c2 ψ := by
  ext a
  simp only [c2, charMap_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.inr_apply,
    AddChar.mul_apply, lt_apply, c1, AddMonoidHom.inl_apply]
  rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp [cu]

theorem c2_charMap_cl (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    c2 (charMap (cl h2 r) ψ) = c2 ψ := by
  ext a; simp [c2, charMap_apply, cl]

theorem c1_charMap_cl (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    c1 (charMap (cl h2 r) ψ) = lt r (c2 ψ) * c1 ψ := by
  ext a
  simp only [c1, charMap_apply, AddChar.compAddMonoidHom_apply, AddMonoidHom.inl_apply,
    AddChar.mul_apply, lt_apply, c2, AddMonoidHom.inr_apply]
  rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp [cl, add_comm]

theorem charMap_cu_invol (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    charMap (cu h2 r) (charMap (cu h2 r) ψ) = ψ := by
  ext a; simp [charMap_apply, cu, add_assoc, h2]

theorem charMap_cl_invol (h2 : ∀ r : R, r + r = 0) (r : R) (ψ : AddChar (R × R) ℂ) :
    charMap (cl h2 r) (charMap (cl h2 r) ψ) = ψ := by
  ext a; simp [charMap_apply, cl, add_assoc, h2]

section Meas
variable {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable (ρ : URep A V)

theorem mu_mono {S T : Finset (AddChar A ℂ)} (h : S ⊆ T) (w : V) : mu ρ S w ≤ mu ρ T w :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => sq_nonneg _)

theorem mu_nonneg (S : Finset (AddChar A ℂ)) (w : V) : 0 ≤ mu ρ S w :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem mu_union_le (S T : Finset (AddChar A ℂ)) (w : V) : mu ρ (S ∪ T) w ≤ mu ρ S w + mu ρ T w := by
  unfold mu
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ ψ ∈ S ∩ T, ‖proj ρ ψ w‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem mu_union_disj (S T : Finset (AddChar A ℂ)) (h : Disjoint S T) (w : V) :
    mu ρ (S ∪ T) w = mu ρ S w + mu ρ T w := by
  unfold mu; rw [Finset.sum_union h]

/-- `‖W a v - v‖² = 4 μ{ψ a ≠ 1}` for an element of order two -/
theorem W_sub_order_two (a : A) (ha : a + a = 0) (w : V) :
    ‖ρ.W a w - w‖ ^ 2 = 4 * mu ρ (Finset.univ.filter fun ψ : AddChar A ℂ => ψ a ≠ 1) w := by
  rw [W_sub_norm_sq, mu, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hsq : ψ a * ψ a = 1 := by rw [← AddChar.map_add_eq_mul, ha, AddChar.map_zero_eq_one]
  split_ifs with h
  · have : ψ a = -1 := by
      have : (ψ a - 1) * (ψ a + 1) = 0 := by ring_nf; rw [sq, hsq]; ring
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd (sub_eq_zero.1 h1) h
      · exact eq_neg_of_add_eq_zero_left h1
    rw [this]; norm_num
  · push Not at h; rw [h]; simp

/-- each nontrivial character value of an order-two element is `-1`, so `|ψ a - 1|² ≤ 4` -/
theorem W_sub_le_nontriv (a : A) (ha : a + a = 0) (w : V) :
    ‖ρ.W a w - w‖ ^ 2 ≤ 4 * mu ρ (Finset.univ.filter fun ψ : AddChar A ℂ => ψ ≠ 1) w := by
  rw [W_sub_order_two ρ a ha]
  have : (Finset.univ.filter fun ψ : AddChar A ℂ => ψ a ≠ 1) ⊆
      (Finset.univ.filter fun ψ : AddChar A ℂ => ψ ≠ 1) := by
    intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
    rintro rfl; exact hψ rfl
  linarith [mu_mono ρ this w]

/-- shift for an involutive transport -/
theorem shift_invol (g : V →L[ℂ] V) (hg : ContinuousLinearMap.adjoint g * g = 1)
    (hg' : g * ContinuousLinearMap.adjoint g = 1) (c : A ≃+ A)
    (hc : ∀ a, g * ρ.W a = ρ.W (c a) * g) (hinv : ∀ ψ, charMap c (charMap c ψ) = ψ)
    (S T : Finset (AddChar A ℂ)) (hST : S.map (charMap c).toEmbedding ⊆ T) (v : V) :
    Real.sqrt (mu ρ S v) ≤ Real.sqrt (mu ρ T v) + ‖g v - v‖ := by
  have h1 := shift ρ g hg hg' c hc (S.map (charMap c).toEmbedding) v
  have h2 : (S.map (charMap c).toEmbedding).map (charMap c).toEmbedding = S := by
    ext ψ; simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨φ, ⟨χ, hχ, rfl⟩, rfl⟩; rw [hinv]; exact hχ
    · intro hψ; exact ⟨charMap c ψ, ⟨ψ, hψ, rfl⟩, hinv ψ⟩
  rw [h2] at h1
  have h3 := Real.sqrt_le_sqrt (mu_mono ρ hST v)
  linarith

end Meas

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- the scalar inequality closing Kassabov's estimate (`k = 2`) -/
theorem final_alg (l u e d ε : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u) (he : 0 ≤ e) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hd' : d ≤ ε ^ 2 / 2)
    (hle : Real.sqrt l ≤ Real.sqrt e + ε) (hue : Real.sqrt u ≤ Real.sqrt e + ε)
    (h1 : Real.sqrt (l + e) ≤ Real.sqrt (u + d) + Real.sqrt 2 * ε)
    (h2 : Real.sqrt (u + e) ≤ Real.sqrt (l + d) + Real.sqrt 2 * ε) :
    l + u + e + d ≤ 81 * ε ^ 2 := by
  set L := Real.sqrt l; set U := Real.sqrt u; set Ee := Real.sqrt e; set Dd := Real.sqrt d
  set r2 := Real.sqrt 2
  have hL2 : L ^ 2 = l := Real.sq_sqrt hl
  have hU2 : U ^ 2 = u := Real.sq_sqrt hu
  have hE2 : Ee ^ 2 = e := Real.sq_sqrt he
  have hD2 : Dd ^ 2 = d := Real.sq_sqrt hd
  have hr2 : r2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hU0 : 0 ≤ U := Real.sqrt_nonneg _
  have hE0 : 0 ≤ Ee := Real.sqrt_nonneg _
  have hD0 : 0 ≤ Dd := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r2 := Real.sqrt_nonneg _
  have hr_lo : 1.414 ≤ r2 := by
    rw [show (1.414 : ℝ) = Real.sqrt (1.414 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hr_hi : r2 ≤ 1.4143 := by
    rw [show (1.4143 : ℝ) = Real.sqrt (1.4143 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hud : Real.sqrt (u + d) ≤ U + Dd := sqrt_add_le' hu hd
  have hld : Real.sqrt (l + d) ≤ L + Dd := sqrt_add_le' hl hd
  have hsud : Real.sqrt (u + d) ^ 2 = u + d := Real.sq_sqrt (by linarith)
  have hsld : Real.sqrt (l + d) ^ 2 = l + d := Real.sq_sqrt (by linarith)
  have hsle : Real.sqrt (l + e) ^ 2 = l + e := Real.sq_sqrt (by linarith)
  have hsue : Real.sqrt (u + e) ^ 2 = u + e := Real.sq_sqrt (by linarith)
  have s1 : l + e ≤ u + d + 2 * r2 * ε * (U + Dd) + 2 * ε ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [hsle] at h
    have : 0 ≤ Real.sqrt (u + d) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hud (by positivity : (0:ℝ) ≤ 2 * r2 * ε)]
  have s2 : u + e ≤ l + d + 2 * r2 * ε * (L + Dd) + 2 * ε ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rw [hsue] at h
    have : 0 ≤ Real.sqrt (l + d) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hld (by positivity : (0:ℝ) ≤ 2 * r2 * ε)]
  have hDd : r2 * Dd ≤ ε := by
    have : (r2 * Dd) ^ 2 ≤ ε ^ 2 := by rw [mul_pow, hr2, hD2]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hε (by norm_num)).1 this
  have s5 : e ≤ 2 * r2 * ε * Ee + (9 / 2 + 2 * r2) * ε ^ 2 := by
    have t1 := mul_le_mul_of_nonneg_left hue (by positivity : (0:ℝ) ≤ r2 * ε)
    have t2 := mul_le_mul_of_nonneg_left hle (by positivity : (0:ℝ) ≤ r2 * ε)
    have t3 := mul_le_mul_of_nonneg_left hDd hε
    linarith
  have s6 : Ee ≤ 4.47 * ε := by
    by_contra hcon
    push Not at hcon
    have hEpos : 0 < Ee := lt_of_le_of_lt (by positivity) hcon
    have ha : 4.47 * ε * Ee < Ee * Ee := mul_lt_mul_of_pos_right hcon hEpos
    have hb : r2 * ε * Ee ≤ 1.4143 * ε * Ee :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr_hi hε) hE0
    have hc : 4.47 * ε * ε ≤ Ee * ε := mul_le_mul_of_nonneg_right hcon.le hε
    have hd2 : r2 * ε ^ 2 ≤ 1.4143 * ε ^ 2 := mul_le_mul_of_nonneg_right hr_hi (sq_nonneg _)
    rw [← hE2] at s5
    nlinarith
  have hl' : l ≤ (5.47 * ε) ^ 2 := by
    rw [← hL2]; exact pow_le_pow_left₀ hL0 (by linarith) 2
  have hu' : u ≤ (5.47 * ε) ^ 2 := by
    rw [← hU2]; exact pow_le_pow_left₀ hU0 (by linarith) 2
  have he' : e ≤ (4.47 * ε) ^ 2 := by
    rw [← hE2]; exact pow_le_pow_left₀ hE0 s6 2
  linarith

theorem two_piece_alg (a0 a1 b0 b1 ε : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hε : 0 ≤ ε) (h0 : Real.sqrt a0 ≤ Real.sqrt b0 + ε) (h1 : Real.sqrt a1 ≤ Real.sqrt b1 + ε) :
    Real.sqrt (a0 + a1) ≤ Real.sqrt (b0 + b1) + Real.sqrt 2 * ε := by
  rw [Real.sqrt_le_left (by positivity)]
  have e0 := Real.sq_sqrt ha0; have e1 := Real.sq_sqrt ha1
  have f0 := Real.sq_sqrt hb0; have f1 := Real.sq_sqrt hb1
  have g := Real.sq_sqrt (show (0:ℝ) ≤ b0 + b1 by positivity)
  have r := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have s0 := Real.sqrt_nonneg a0; have s1 := Real.sqrt_nonneg a1
  have t0 := Real.sqrt_nonneg b0; have t1 := Real.sqrt_nonneg b1
  have tg := Real.sqrt_nonneg (b0 + b1); have tr := Real.sqrt_nonneg 2
  have q0 : a0 ≤ (Real.sqrt b0 + ε) ^ 2 := by rw [← e0]; exact pow_le_pow_left₀ s0 h0 2
  have q1 : a1 ≤ (Real.sqrt b1 + ε) ^ 2 := by rw [← e1]; exact pow_le_pow_left₀ s1 h1 2
  have hqm : Real.sqrt b0 + Real.sqrt b1 ≤ Real.sqrt 2 * Real.sqrt (b0 + b1) := by
    rw [← Real.sqrt_mul (by norm_num)]
    rw [Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sqrt b0 - Real.sqrt b1)]
  rw [add_sq, mul_pow, r, g]
  rw [add_sq, f0] at q0
  rw [add_sq, f1] at q1
  have := mul_le_mul_of_nonneg_left hqm (by positivity : (0:ℝ) ≤ 2 * ε)
  nlinarith

end KasA



open scoped InnerProductSpace
open KasF KasV KasA

namespace KasA

variable {R : Type} [Ring R] [Fintype R] [DecidableEq R]

/-- the generator values: `none ↦ 1`, `some i ↦ x i` -/
def gen (x : Fin 2 → R) : Option (Fin 2) → R
  | none => 1
  | some i => x i

section Main
variable (h2 : ∀ r : R, r + r = 0) (x : Fin 2 → R) (N : ℕ) (hN : Rn x N = ⊤)
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable (ρ : URep (R × R) V)

/-- the partition of characters by the valuations of their two components -/
noncomputable def ν1 (ψ : AddChar (R × R) ℂ) : ℕ := nu x N (c1 ψ)
noncomputable def ν2 (ψ : AddChar (R × R) ℂ) : ℕ := nu x N (c2 ψ)

noncomputable def Dset : Finset (AddChar (R × R) ℂ) :=
  Finset.univ.filter fun ψ => ν1 x N ψ = 0 ∨ ν2 x N ψ = 0
noncomputable def Lset : Finset (AddChar (R × R) ℂ) :=
  Finset.univ.filter fun ψ => 0 < ν1 x N ψ ∧ ν1 x N ψ < ν2 x N ψ
noncomputable def Eset : Finset (AddChar (R × R) ℂ) :=
  Finset.univ.filter fun ψ => 0 < ν1 x N ψ ∧ ν1 x N ψ = ν2 x N ψ ∧ ν1 x N ψ ≤ N
noncomputable def Uset : Finset (AddChar (R × R) ℂ) :=
  Finset.univ.filter fun ψ => 0 < ν2 x N ψ ∧ ν2 x N ψ < ν1 x N ψ

theorem mem_D (ψ : AddChar (R × R) ℂ) : ψ ∈ Dset x N ↔ ν1 x N ψ = 0 ∨ ν2 x N ψ = 0 := by
  unfold Dset; rw [Finset.mem_filter]; simp
theorem mem_L (ψ : AddChar (R × R) ℂ) : ψ ∈ Lset x N ↔ 0 < ν1 x N ψ ∧ ν1 x N ψ < ν2 x N ψ := by
  unfold Lset; rw [Finset.mem_filter]; simp
theorem mem_E (ψ : AddChar (R × R) ℂ) :
    ψ ∈ Eset x N ↔ 0 < ν1 x N ψ ∧ ν1 x N ψ = ν2 x N ψ ∧ ν1 x N ψ ≤ N := by
  unfold Eset; rw [Finset.mem_filter]; simp
theorem mem_U (ψ : AddChar (R × R) ℂ) : ψ ∈ Uset x N ↔ 0 < ν2 x N ψ ∧ ν2 x N ψ < ν1 x N ψ := by
  unfold Uset; rw [Finset.mem_filter]; simp

theorem disj_LE : Disjoint (Lset x N) (Eset x N) := by
  unfold Lset Eset; rw [Finset.disjoint_filter]; intro ψ _ h1 h2; omega
theorem disj_UE : Disjoint (Uset x N) (Eset x N) := by
  unfold Uset Eset; rw [Finset.disjoint_filter]; intro ψ _ h1 h2; omega
theorem disj_UD : Disjoint (Uset x N) (Dset x N) := by
  unfold Uset Dset; rw [Finset.disjoint_filter]; intro ψ _ h1 h2; omega
theorem disj_LD : Disjoint (Lset x N) (Dset x N) := by
  unfold Lset Dset; rw [Finset.disjoint_filter]; intro ψ _ h1 h2; omega

include hN in
theorem cover : (Finset.univ.filter fun ψ : AddChar (R × R) ℂ => ψ ≠ 1) ⊆
    Dset x N ∪ Lset x N ∪ Eset x N ∪ Uset x N := by
  intro ψ hψ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ
  simp only [Finset.mem_union, Dset, Lset, Eset, Uset, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := nu_le (N := N) x (c1 ψ)
  have h2' := nu_le (N := N) x (c2 ψ)
  by_cases hE : ν1 x N ψ = N + 1 ∧ ν2 x N ψ = N + 1
  · exfalso; apply hψ
    rw [char_eq_one_iff]
    exact ⟨(nu_eq_top_iff x hN _).1 hE.1, (nu_eq_top_iff x hN _).1 hE.2⟩
  · unfold ν1 ν2 at *; omega

theorem lt_one (ψ : AddChar R ℂ) : lt (1 : R) ψ = ψ := by ext a; simp [lt_apply]

theorem mapL_sub_E : (Lset x N).map (charMap (cu h2 1)).toEmbedding ⊆ Eset x N := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 hφ
  rw [mem_L] at hψ; rw [mem_E]
  simp only [ν1, ν2] at hψ ⊢
  simp only [Equiv.toEmbedding_apply, c1_charMap_cu, c2_charMap_cu, lt_one]
  have := nu_mul (N := N) x (c1 ψ) (c2 ψ) hψ.2
  have h3 := nu_le (N := N) x (c2 ψ)
  refine ⟨hψ.1, this.symm, by omega⟩

theorem mapU_sub_E : (Uset x N).map (charMap (cl h2 1)).toEmbedding ⊆ Eset x N := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 hφ
  rw [mem_U] at hψ; rw [mem_E]
  simp only [ν1, ν2] at hψ ⊢
  simp only [Equiv.toEmbedding_apply, c1_charMap_cl, c2_charMap_cl, lt_one]
  have := nu_mul (N := N) x (c2 ψ) (c1 ψ) hψ.2
  have h3 := nu_le (N := N) x (c1 ψ)
  refine ⟨by omega, by omega, by omega⟩

/-- selection of a generator lowering the valuation of a character of `R` -/
noncomputable def sel (ψ : AddChar R ℂ) : Fin 2 :=
  if nu x N (lt (x 0) ψ) = nu x N ψ - 1 then 0 else 1

include hN in
theorem sel_spec (ψ : AddChar R ℂ) (h0 : 0 < nu x N ψ) (hN' : nu x N ψ ≤ N) :
    nu x N (lt (x (sel x N ψ)) ψ) = nu x N ψ - 1 := by
  unfold sel
  split_ifs with h
  · exact h
  · obtain ⟨i, hi⟩ := nu_lt_exists x hN ψ h0 hN'
    fin_cases i
    · exact absurd hi h
    · exact hi

include hN in
theorem mapLE_piece (i : Fin 2) :
    ((Lset x N ∪ Eset x N).filter fun ψ => sel x N (c1 ψ) = i).map
      (charMap (cu h2 (x i))).toEmbedding ⊆ Uset x N ∪ Dset x N := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 hφ
  rw [Finset.mem_filter, Finset.mem_union, mem_L, mem_E] at hψ
  rw [Finset.mem_union, mem_U, mem_D]
  simp only [ν1, ν2, Equiv.toEmbedding_apply, c1_charMap_cu, c2_charMap_cu] at hψ ⊢
  obtain ⟨hLE, hsel⟩ := hψ
  have hpos : 0 < nu x N (c1 ψ) := by rcases hLE with h | h <;> exact h.1
  have hle : nu x N (c1 ψ) ≤ N := by
    rcases hLE with h | h
    · have := nu_le (N := N) x (c2 ψ); omega
    · exact h.2.2
  have hle2 : nu x N (c1 ψ) ≤ nu x N (c2 ψ) := by rcases hLE with h | h <;> omega
  have hs := sel_spec x N hN (c1 ψ) hpos hle
  rw [hsel] at hs
  have hm := nu_mul (N := N) x (lt (x i) (c1 ψ)) (c2 ψ) (by omega)
  rw [hm, hs]
  omega

include hN in
theorem mapLE_disj :
    Disjoint (((Lset x N ∪ Eset x N).filter fun ψ => sel x N (c1 ψ) = 0).map
      (charMap (cu h2 (x 0))).toEmbedding)
      (((Lset x N ∪ Eset x N).filter fun ψ => sel x N (c1 ψ) = 1).map
      (charMap (cu h2 (x 1))).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro φ h0 h1
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 h0
  obtain ⟨ψ', hψ', he⟩ := Finset.mem_map.1 h1
  simp only [Finset.mem_filter] at hψ hψ'
  have : c1 ψ' = c1 ψ := by
    have := congrArg c1 he
    simp only [Equiv.toEmbedding_apply, c1_charMap_cu] at this
    exact this
  rw [this, hψ.2] at hψ'
  exact absurd hψ'.2 (by decide)

include hN in
theorem mapUE_piece (i : Fin 2) :
    ((Uset x N ∪ Eset x N).filter fun ψ => sel x N (c2 ψ) = i).map
      (charMap (cl h2 (x i))).toEmbedding ⊆ Lset x N ∪ Dset x N := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 hφ
  rw [Finset.mem_filter, Finset.mem_union, mem_U, mem_E] at hψ
  rw [Finset.mem_union, mem_L, mem_D]
  simp only [ν1, ν2, Equiv.toEmbedding_apply, c1_charMap_cl, c2_charMap_cl] at hψ ⊢
  obtain ⟨hUE, hsel⟩ := hψ
  have hpos : 0 < nu x N (c2 ψ) := by rcases hUE with h | h <;> omega
  have hle : nu x N (c2 ψ) ≤ N := by
    rcases hUE with h | h
    · have := nu_le (N := N) x (c1 ψ); omega
    · omega
  have hle2 : nu x N (c2 ψ) ≤ nu x N (c1 ψ) := by rcases hUE with h | h <;> omega
  have hs := sel_spec x N hN (c2 ψ) hpos hle
  rw [hsel] at hs
  have hm := nu_mul (N := N) x (lt (x i) (c2 ψ)) (c1 ψ) (by omega)
  rw [hm, hs]
  omega

theorem mapUE_disj :
    Disjoint (((Uset x N ∪ Eset x N).filter fun ψ => sel x N (c2 ψ) = 0).map
      (charMap (cl h2 (x 0))).toEmbedding)
      (((Uset x N ∪ Eset x N).filter fun ψ => sel x N (c2 ψ) = 1).map
      (charMap (cl h2 (x 1))).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro φ h0 h1
  obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_map.1 h0
  obtain ⟨ψ', hψ', he⟩ := Finset.mem_map.1 h1
  simp only [Finset.mem_filter] at hψ hψ'
  have : c2 ψ' = c2 ψ := by
    have := congrArg c2 he
    simp only [Equiv.toEmbedding_apply, c2_charMap_cl] at this
    exact this
  rw [this, hψ.2] at hψ'
  exact absurd hψ'.2 (by decide)

/-- two-piece shift: `√μ(S) ≤ √μ(T) + √2 ε` -/
theorem two_piece (S T : Finset (AddChar (R × R) ℂ)) (p : AddChar (R × R) ℂ → Prop) [DecidablePred p]
    (g0 g1 : V →L[ℂ] V) (c0 c1' : (R × R) ≃+ (R × R))
    (hg0 : ContinuousLinearMap.adjoint g0 * g0 = 1) (hg0' : g0 * ContinuousLinearMap.adjoint g0 = 1)
    (hg1 : ContinuousLinearMap.adjoint g1 * g1 = 1) (hg1' : g1 * ContinuousLinearMap.adjoint g1 = 1)
    (hc0 : ∀ a, g0 * ρ.W a = ρ.W (c0 a) * g0) (hc1 : ∀ a, g1 * ρ.W a = ρ.W (c1' a) * g1)
    (hi0 : ∀ ψ, charMap c0 (charMap c0 ψ) = ψ) (hi1 : ∀ ψ, charMap c1' (charMap c1' ψ) = ψ)
    (hsub0 : (S.filter p).map (charMap c0).toEmbedding ⊆ T)
    (hsub1 : (S.filter fun ψ => ¬ p ψ).map (charMap c1').toEmbedding ⊆ T)
    (hdisj : Disjoint ((S.filter p).map (charMap c0).toEmbedding)
      ((S.filter fun ψ => ¬ p ψ).map (charMap c1').toEmbedding))
    (v : V) (ε : ℝ) (hε : 0 ≤ ε) (h0 : ‖g0 v - v‖ ≤ ε) (h1 : ‖g1 v - v‖ ≤ ε) :
    Real.sqrt (mu ρ S v) ≤ Real.sqrt (mu ρ T v) + Real.sqrt 2 * ε := by
  set M0 := (S.filter p).map (charMap c0).toEmbedding
  set M1 := (S.filter fun ψ => ¬ p ψ).map (charMap c1').toEmbedding
  have e0 := shift_invol ρ g0 hg0 hg0' c0 hc0 hi0 (S.filter p) M0 (subset_refl _) v
  have e1 := shift_invol ρ g1 hg1 hg1' c1' hc1 hi1 (S.filter fun ψ => ¬ p ψ) M1 (subset_refl _) v
  have hS : mu ρ S v = mu ρ (S.filter p) v + mu ρ (S.filter fun ψ => ¬ p ψ) v := by
    unfold mu; rw [Finset.sum_filter_add_sum_filter_not]
  have hT : mu ρ M0 v + mu ρ M1 v ≤ mu ρ T v := by
    rw [← mu_union_disj ρ M0 M1 hdisj]
    exact mu_mono ρ (Finset.union_subset hsub0 hsub1) v
  rw [hS]
  have := two_piece_alg _ _ _ _ ε (mu_nonneg ρ _ v) (mu_nonneg ρ _ v) (mu_nonneg ρ M0 v)
    (mu_nonneg ρ M1 v) hε (e0.trans (by linarith)) (e1.trans (by linarith))
  exact this.trans (by linarith [Real.sqrt_le_sqrt hT])

include hN in
/-- **Relative property (T) in characteristic two** (Kassabov, Theorem 2.2 and Corollary 2.8,
specialized to a finite ring of characteristic `2` generated by two elements) -/
theorem relT_main
    (gu gl : Option (Fin 2) → (V →L[ℂ] V))
    (hgu : ∀ j, ContinuousLinearMap.adjoint (gu j) * gu j = 1)
    (hgu' : ∀ j, gu j * ContinuousLinearMap.adjoint (gu j) = 1)
    (hgl : ∀ j, ContinuousLinearMap.adjoint (gl j) * gl j = 1)
    (hgl' : ∀ j, gl j * ContinuousLinearMap.adjoint (gl j) = 1)
    (hcu : ∀ j a, gu j * ρ.W a = ρ.W (cu h2 (gen x j) a) * gu j)
    (hcl : ∀ j a, gl j * ρ.W a = ρ.W (cl h2 (gen x j) a) * gl j)
    (v : V) (ε : ℝ) (hε : 0 ≤ ε)
    (h10 : ‖ρ.W (1, 0) v - v‖ ≤ ε) (h01 : ‖ρ.W (0, 1) v - v‖ ≤ ε)
    (hu : ∀ j, ‖gu j v - v‖ ≤ ε) (hl : ∀ j, ‖gl j v - v‖ ≤ ε) (a : R × R) :
    ‖ρ.W a v - v‖ ≤ 18 * ε := by
  -- the four masses
  set l := mu ρ (Lset x N) v
  set u := mu ρ (Uset x N) v
  set e := mu ρ (Eset x N) v
  set d := mu ρ (Dset x N) v
  -- (1) the mass of D
  have hd : d ≤ ε ^ 2 / 2 := by
    have hsub : Dset x N ⊆ (Finset.univ.filter fun ψ : AddChar (R × R) ℂ => ψ (1, 0) ≠ 1) ∪
        (Finset.univ.filter fun ψ : AddChar (R × R) ℂ => ψ (0, 1) ≠ 1) := by
      intro ψ hψ
      rw [mem_D] at hψ
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hψ with h | h
      · left; have := (nu_eq_zero_iff (N := N) x (c1 ψ)).1 h; exact this
      · right; have := (nu_eq_zero_iff (N := N) x (c2 ψ)).1 h; exact this
    have q1 := W_sub_order_two ρ (1, 0) (by ext <;> simp [h2]) v
    have q2 := W_sub_order_two ρ (0, 1) (by ext <;> simp [h2]) v
    have r1 : ‖ρ.W (1, 0) v - v‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h10 2
    have r2 : ‖ρ.W (0, 1) v - v‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h01 2
    have := (mu_mono ρ hsub v).trans (mu_union_le ρ _ _ v)
    simp only [d]
    linarith
  -- (2) L and U against E
  have hle : Real.sqrt l ≤ Real.sqrt e + ε :=
    (shift_invol ρ (gu none) (hgu none) (hgu' none) (cu h2 1) (hcu none) (charMap_cu_invol h2 1)
      (Lset x N) (Eset x N) (mapL_sub_E h2 x N) v).trans (by linarith [hu none])
  have hue : Real.sqrt u ≤ Real.sqrt e + ε :=
    (shift_invol ρ (gl none) (hgl none) (hgl' none) (cl h2 1) (hcl none) (charMap_cl_invol h2 1)
      (Uset x N) (Eset x N) (mapU_sub_E h2 x N) v).trans (by linarith [hl none])
  -- (3) the two-piece estimates
  have hsel0 : ∀ i : Fin 2, ¬ (i = 0) → i = 1 := by decide
  have h3 : Real.sqrt (mu ρ (Lset x N ∪ Eset x N) v) ≤ Real.sqrt (mu ρ (Uset x N ∪ Dset x N) v) +
      Real.sqrt 2 * ε := by
    refine two_piece ρ (Lset x N ∪ Eset x N) (Uset x N ∪ Dset x N) (fun ψ => sel x N (c1 ψ) = 0)
      (gu (some 0)) (gu (some 1)) (cu h2 (x 0)) (cu h2 (x 1)) (hgu _) (hgu' _) (hgu _) (hgu' _)
      (hcu (some 0)) (hcu (some 1)) (charMap_cu_invol h2 _) (charMap_cu_invol h2 _)
      (mapLE_piece h2 x N hN 0) ?_ ?_ v ε hε (hu _) (hu _)
    · have := mapLE_piece h2 x N hN 1
      convert this using 3
      constructor
      · intro h; exact hsel0 _ h
      · intro h; rw [h]; decide
    · have := mapLE_disj h2 x N hN
      convert this using 3
      constructor
      · intro h; exact hsel0 _ h
      · intro h; rw [h]; decide
  have h4 : Real.sqrt (mu ρ (Uset x N ∪ Eset x N) v) ≤ Real.sqrt (mu ρ (Lset x N ∪ Dset x N) v) +
      Real.sqrt 2 * ε := by
    refine two_piece ρ (Uset x N ∪ Eset x N) (Lset x N ∪ Dset x N) (fun ψ => sel x N (c2 ψ) = 0)
      (gl (some 0)) (gl (some 1)) (cl h2 (x 0)) (cl h2 (x 1)) (hgl _) (hgl' _) (hgl _) (hgl' _)
      (hcl (some 0)) (hcl (some 1)) (charMap_cl_invol h2 _) (charMap_cl_invol h2 _)
      (mapUE_piece h2 x N hN 0) ?_ ?_ v ε hε (hl _) (hl _)
    · have := mapUE_piece h2 x N hN 1
      convert this using 3
      constructor
      · intro h; exact hsel0 _ h
      · intro h; rw [h]; decide
    · have := mapUE_disj h2 x N
      convert this using 3
      constructor
      · intro h; exact hsel0 _ h
      · intro h; rw [h]; decide
  rw [mu_union_disj ρ _ _ (disj_LE x N), mu_union_disj ρ _ _ (disj_UD x N)] at h3
  rw [mu_union_disj ρ _ _ (disj_UE x N), mu_union_disj ρ _ _ (disj_LD x N)] at h4
  have htot := final_alg l u e d ε (mu_nonneg ρ _ v) (mu_nonneg ρ _ v) (mu_nonneg ρ _ v)
    (mu_nonneg ρ _ v) hε hd hle hue h3 h4
  have hNZ : mu ρ (Finset.univ.filter fun ψ : AddChar (R × R) ℂ => ψ ≠ 1) v ≤ d + l + e + u := by
    refine (mu_mono ρ (cover x N hN) v).trans ?_
    refine (mu_union_le ρ _ _ v).trans ?_
    have := mu_union_le ρ (Dset x N ∪ Lset x N) (Eset x N) v
    have := mu_union_le ρ (Dset x N) (Lset x N) v
    linarith
  have hW := W_sub_le_nontriv ρ a (by ext <;> simp [h2]) v
  have hsq : ‖ρ.W a v - v‖ ^ 2 ≤ (18 * ε) ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq

end Main

end KasA



open KasV

namespace KasGen

theorem pow_mem_Rn {R : Type} [Ring R] [Fintype R] [DecidableEq R] (x : Fin 2 → R) (p : ℕ) : x 0 ^ p ∈ Rn x p := by
  induction p with
  | zero => simpa using one_mem_Rn x 0
  | succ p ih => rw [pow_succ']; exact mul_mem_Rn x p 0 _ ih

theorem word_mem_Rn {R : Type} [Ring R] [Fintype R] [DecidableEq R] (x : Fin 2 → R) (p q : ℕ) :
    x 0 ^ p * x 1 * x 0 ^ q ∈ Rn x (p + (q + 1)) := by
  induction p with
  | zero =>
    simpa using mul_mem_Rn x q 1 _ (pow_mem_Rn x q)
  | succ p ih =>
    rw [pow_succ', mul_assoc, mul_assoc, show p + 1 + (q + 1) = (p + (q + 1)) + 1 by omega]
    refine mul_mem_Rn x _ 0 _ ?_
    rw [← mul_assoc]; exact ih

variable {s : ℕ}

theorem A_pow_apply (hs : 1 ≤ s) (p : ℕ) (i j : Fin s) :
    (DepthOneQExp.kassabovA s ^ p) i j = if (j : ℕ) = ((i : ℕ) + p) % s then 1 else 0 := by
  induction p generalizing j with
  | zero =>
    rw [pow_zero, Matrix.one_apply, add_zero, Nat.mod_eq_of_lt i.2]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'.symm))]
  | succ p ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single ⟨((i : ℕ) + p) % s, Nat.mod_lt _ (by omega)⟩]
    · rw [ih]
      simp only [DepthOneQExp.kassabovA, if_true, one_mul]
      rw [Nat.mod_add_mod, add_assoc]
    · intro k _ hk
      rw [ih, if_neg, zero_mul]
      intro h; exact hk (Fin.ext h)
    · simp

theorem unit_eq (hs : 1 ≤ s) (i0 j0 : Fin s) :
    DepthOneQExp.kassabovA s ^ (s - (i0 : ℕ)) * DepthOneQExp.kassabovB s *
      DepthOneQExp.kassabovA s ^ (j0 : ℕ) = Matrix.single i0 j0 1 := by
  have h0 : (0 : ℕ) < s := by omega
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨0, h0⟩]
  · rw [Matrix.mul_apply, Finset.sum_eq_single ⟨0, h0⟩]
    · rw [A_pow_apply hs, A_pow_apply hs]
      simp only [DepthOneQExp.kassabovB, and_self, if_true, mul_one, zero_add,
        Nat.mod_eq_of_lt j0.2, Matrix.single_apply]
      have key : ((i : ℕ) + (s - (i0 : ℕ))) % s = 0 ↔ i = i0 := by
        have hi := i.2; have hi0 := i0.2
        rw [Fin.ext_iff]
        by_cases hle : (i0 : ℕ) ≤ i
        · rw [show (i : ℕ) + (s - i0) = (i - i0) + s by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]
          omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      by_cases h1 : i = i0
      · subst h1
        simp only [true_and]
        rw [if_pos (key.2 rfl).symm]
        by_cases h2 : j0 = j
        · subst h2; simp
        · rw [if_neg (fun h => h2 (Fin.ext h.symm)), if_neg h2, mul_zero]
      · rw [if_neg (fun h => h1 (key.1 h.symm)), zero_mul, if_neg (fun h => h1 h.1.symm)]
    · intro k _ hk
      simp only [DepthOneQExp.kassabovB]
      rw [if_neg (fun h => hk (Fin.ext h.1)), mul_zero]
    · simp
  · intro k _ hk
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro m _
    simp only [DepthOneQExp.kassabovB]
    rw [if_neg (fun h => hk (Fin.ext h.2)), mul_zero]
  · simp

theorem single_mem (S : AddSubgroup (Matrix (Fin s) (Fin s) (ZMod 2)))
    (h : ∀ i j, Matrix.single i j (1 : ZMod 2) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  have : Matrix.single i j (M i j) = (M i j).val • Matrix.single i j (1 : ZMod 2) := by
    rw [Matrix.smul_single, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [this]
  exact S.nsmul_mem (h i j) _

theorem gen_top (hs : 1 ≤ s) :
    Rn (![DepthOneQExp.kassabovA s, DepthOneQExp.kassabovB s]) (2 * s) = ⊤ := by
  apply single_mem
  intro i j
  rw [← unit_eq hs]
  refine Rn_mono _ ?_ (word_mem_Rn _ (s - (i : ℕ)) j)
  have := j.2; omega

instance instFintypeMulOpp {α : Type} [Fintype α] : Fintype αᵐᵒᵖ :=
  Fintype.ofEquiv α MulOpposite.opEquiv

theorem gen_top_op (hs : 1 ≤ s) :
    Rn (![MulOpposite.op (DepthOneQExp.kassabovA s), MulOpposite.op (DepthOneQExp.kassabovB s)])
      (2 * s) = ⊤ := by
  set S := Rn (![MulOpposite.op (DepthOneQExp.kassabovA s), MulOpposite.op (DepthOneQExp.kassabovB s)])
      (2 * s)
  have h : S.comap (MulOpposite.opAddEquiv : Matrix (Fin s) (Fin s) (ZMod 2) ≃+ _).toAddMonoidHom = ⊤ := by
    apply single_mem
    intro i j
    rw [← unit_eq hs]
    show MulOpposite.op _ ∈ S
    rw [MulOpposite.op_mul, MulOpposite.op_mul, MulOpposite.op_pow, MulOpposite.op_pow, ← mul_assoc]
    refine Rn_mono _ ?_ (word_mem_Rn _ (j : ℕ) (s - (i : ℕ)))
    have := j.2; omega
  rw [eq_top_iff]
  intro M _
  have : MulOpposite.unop M ∈ S.comap (MulOpposite.opAddEquiv : Matrix (Fin s) (Fin s) (ZMod 2) ≃+ _).toAddMonoidHom := by
    rw [h]; trivial
  exact this

end KasGen



open DepthOneQExp Matrix

namespace KasBlk

variable {s : ℕ}

abbrev SLs (s : ℕ) := Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)
abbrev Ms (s : ℕ) := Matrix (Fin s) (Fin s) (ZMod 2)

def Nb (s : ℕ) (a b : Fin 3) (r : Ms s) :
    Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2) :=
  Matrix.of fun p q => if p.1 = a ∧ q.1 = b then r p.2 q.2 else 0

theorem Nb_mul_Nb (a b c d : Fin 3) (r t : Ms s) :
    Nb s a b r * Nb s c d t = if b = c then Nb s a d (r * t) else 0 := by
  ext p q
  simp only [Nb, mul_apply, of_apply]
  split_ifs with hbc
  · subst hbc
    simp only [of_apply]
    by_cases hpa : p.1 = a <;> by_cases hqd : q.1 = d
    · simp only [hpa, hqd, true_and, and_true]
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc; simp [hc]
      · simp
    all_goals simp [hpa, hqd]
  · simp only [Matrix.zero_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases h1 : x.1 = b
    · have : ¬ (x.1 = c) := fun h => hbc (h1.symm.trans h)
      simp [this]
    · simp [h1]

theorem Nb_add (a b : Fin 3) (r t : Ms s) : Nb s a b (r + t) = Nb s a b r + Nb s a b t := by
  ext p q; simp only [Nb, of_apply, Matrix.add_apply]; split_ifs <;> simp

theorem Nb_sub (a b : Fin 3) (r t : Ms s) : Nb s a b (r - t) = Nb s a b r - Nb s a b t := by
  ext p q; simp only [Nb, of_apply, Matrix.sub_apply]; split_ifs <;> simp

theorem Nb_zero (a b : Fin 3) : Nb s a b 0 = 0 := by
  ext p q; simp only [Nb, of_apply, Matrix.zero_apply]; split_ifs <;> rfl

theorem neg_Ms (r : Ms s) : -r = r := by
  ext i j; simp only [Matrix.neg_apply]; exact ZMod.neg_eq_self_mod_two _

theorem add_eq_sub (r t : Ms s) : r + t = r - t := by
  rw [sub_eq_add_neg, neg_Ms]

theorem two_Ms (r : Ms s) : r + r = 0 := by
  ext i j; simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize r i j = c; revert c; decide

def E (a b : Fin 3) (h : a ≠ b) (r : Ms s) : SLs s := ⟨blockElem s a b r, det_blockElem s h r⟩

abbrev ι (s : ℕ) := Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (finProdFinEquiv (m := 3) (n := s))

theorem coe_E (a b : Fin 3) (h : a ≠ b) (r : Ms s) :
    ((E a b h r : SLs s) : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) = ι s (1 + Nb s a b r) := by
  rw [Matrix.coe_reindexAlgEquiv]; rfl

theorem E_zero (a b : Fin 3) (h : a ≠ b) : (E a b h 0 : SLs s) = 1 := by
  apply Subtype.ext
  rw [coe_E, Nb_zero, add_zero, map_one]; rfl


-- column 3
theorem c3_add (a b c d : Ms s) :
    E 0 2 (by decide) (a + c) * E 1 2 (by decide) (b + d) =
      (E 0 2 (by decide) a * E 1 2 (by decide) b) * (E 0 2 (by decide) c * E 1 2 (by decide) d) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem c3_u (r a b : Ms s) :
    E 0 1 (by decide) r * (E 0 2 (by decide) a * E 1 2 (by decide) b) =
      (E 0 2 (by decide) (a + r * b) * E 1 2 (by decide) b) * E 0 1 (by decide) r := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem c3_l (r a b : Ms s) :
    E 1 0 (by decide) r * (E 0 2 (by decide) a * E 1 2 (by decide) b) =
      (E 0 2 (by decide) a * E 1 2 (by decide) (b + r * a)) * E 1 0 (by decide) r := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

-- row 1 (sign-sensitive)
theorem r1_u (r a b : Ms s) :
    E 2 1 (by decide) r * (E 0 1 (by decide) a * E 0 2 (by decide) b) =
      (E 0 1 (by decide) (a + b * r) * E 0 2 (by decide) b) * E 2 1 (by decide) r := by
  rw [add_eq_sub]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem c3_0 : (E 0 2 (by decide) 0 * E 1 2 (by decide) 0 : SLs s) = 1 := by
  rw [E_zero, E_zero, mul_one]

-- column 1
theorem c1_add (a b c d : Ms s) :
    E 1 0 (by decide) (a + c) * E 2 0 (by decide) (b + d) =
      (E 1 0 (by decide) a * E 2 0 (by decide) b) * (E 1 0 (by decide) c * E 2 0 (by decide) d) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem c1_u (r a b : Ms s) :
    E 1 2 (by decide) r * (E 1 0 (by decide) a * E 2 0 (by decide) b) =
      (E 1 0 (by decide) (a + r * b) * E 2 0 (by decide) b) * E 1 2 (by decide) r := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem c1_l (r a b : Ms s) :
    E 2 1 (by decide) r * (E 1 0 (by decide) a * E 2 0 (by decide) b) =
      (E 1 0 (by decide) a * E 2 0 (by decide) (b + r * a)) * E 2 1 (by decide) r := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

-- row 1
theorem r1_add (a b c d : Ms s) :
    E 0 1 (by decide) (a + c) * E 0 2 (by decide) (b + d) =
      (E 0 1 (by decide) a * E 0 2 (by decide) b) * (E 0 1 (by decide) c * E 0 2 (by decide) d) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem r1_l (r a b : Ms s) :
    E 1 2 (by decide) r * (E 0 1 (by decide) a * E 0 2 (by decide) b) =
      (E 0 1 (by decide) a * E 0 2 (by decide) (b + a * r)) * E 1 2 (by decide) r := by
  rw [add_eq_sub]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

-- row 3
theorem r3_add (a b c d : Ms s) :
    E 2 0 (by decide) (a + c) * E 2 1 (by decide) (b + d) =
      (E 2 0 (by decide) a * E 2 1 (by decide) b) * (E 2 0 (by decide) c * E 2 1 (by decide) d) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem r3_u (r a b : Ms s) :
    E 1 0 (by decide) r * (E 2 0 (by decide) a * E 2 1 (by decide) b) =
      (E 2 0 (by decide) (a + b * r) * E 2 1 (by decide) b) * E 1 0 (by decide) r := by
  rw [add_eq_sub]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

theorem r3_l (r a b : Ms s) :
    E 0 1 (by decide) r * (E 2 0 (by decide) a * E 2 1 (by decide) b) =
      (E 2 0 (by decide) a * E 2 1 (by decide) (b + a * r)) * E 0 1 (by decide) r := by
  rw [add_eq_sub]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  abel

end KasBlk



open scoped InnerProductSpace

namespace KasG
open KasF KasV KasA

theorem relT_group {R : Type} [Ring R] [Fintype R] [DecidableEq R]
    (h2 : ∀ r : R, r + r = 0) (x : Fin 2 → R) (N : ℕ) (hN : Rn x N = ⊤)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {G : Type} [Group G] (U : G → (V →L[ℂ] V)) (hUmul : ∀ g h, U (g * h) = U g * U h)
    (hU1 : U 1 = 1) (hUadj : ∀ g, ContinuousLinearMap.adjoint (U g) = U g⁻¹)
    (τ : R × R → G) (hτ0 : τ 0 = 1) (hτ : ∀ a b, τ (a + b) = τ a * τ b)
    (u l : R → G) (hu : ∀ r a, u r * τ a = τ (cu h2 r a) * u r)
    (hl : ∀ r a, l r * τ a = τ (cl h2 r a) * l r)
    (v : V) (ε : ℝ) (hε : 0 ≤ ε)
    (h10 : ‖U (τ (1, 0)) v - v‖ ≤ ε) (h01 : ‖U (τ (0, 1)) v - v‖ ≤ ε)
    (hu' : ∀ j, ‖U (u (gen x j)) v - v‖ ≤ ε) (hl' : ∀ j, ‖U (l (gen x j)) v - v‖ ≤ ε)
    (a : R × R) : ‖U (τ a) v - v‖ ≤ 18 * ε := by
  have hinv : ∀ a, τ (-a) = (τ a)⁻¹ := fun a => by
    have h : τ a * τ (-a) = 1 := by rw [← hτ, add_neg_cancel, hτ0]
    exact eq_inv_of_mul_eq_one_right h
  have hunit1 : ∀ g, ContinuousLinearMap.adjoint (U g) * U g = 1 := fun g => by
    rw [hUadj, ← hUmul, inv_mul_cancel, hU1]
  have hunit2 : ∀ g, U g * ContinuousLinearMap.adjoint (U g) = 1 := fun g => by
    rw [hUadj, ← hUmul, mul_inv_cancel, hU1]
  let ρ : URep (R × R) V :=
    { W := fun a => U (τ a)
      map_zero := by simp only [hτ0, hU1]
      map_add := fun a b => by simp only [hτ, hUmul]
      adj := fun a => by simp only [hUadj, hinv] }
  exact relT_main h2 x N hN ρ (fun j => U (u (gen x j))) (fun j => U (l (gen x j)))
    (fun j => hunit1 _) (fun j => hunit2 _) (fun j => hunit1 _) (fun j => hunit2 _)
    (fun j a => by simp only [ρ, ← hUmul, hu]) (fun j a => by simp only [ρ, ← hUmul, hl])
    v ε hε h10 h01 hu' hl' a

end KasG

namespace KasSL
open KasF KasV KasA KasG KasGen KasBlk DepthOneQExp

variable {s : ℕ} (ρ : ConstGapCircuits.UnitaryRep (SLs s))

noncomputable def U (g : SLs s) : EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)

theorem U_mul (g h : SLs s) : U ρ (g * h) = U ρ g * U ρ h := by
  simp only [U, map_mul]
  rw [Submonoid.coe_mul, map_mul]

theorem U_one : U ρ 1 = 1 := by simp [U]

theorem U_adj (g : SLs s) : ContinuousLinearMap.adjoint (U ρ g) = U ρ g⁻¹ := by
  simp only [U]
  rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, map_star,
    ContinuousLinearMap.star_eq_adjoint]

theorem two_op (r : (Ms s)ᵐᵒᵖ) : r + r = 0 :=
  MulOpposite.unop_injective (by rw [MulOpposite.unop_add, two_Ms, MulOpposite.unop_zero])

section
variable (hs : 1 ≤ s) (v : EuclideanSpace ℂ (Fin ρ.dim)) (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ∀ i : Fin 14, ‖U ρ (sigma s i) v - v‖ ≤ ε)
include hs hε hv

theorem inst_c3 (r₁ r₂ : Ms s) :
    ‖U ρ (E 0 2 (by decide) r₁ * E 1 2 (by decide) r₂) v - v‖ ≤ 18 * ε := by
  refine relT_group (R := Ms s) two_Ms ![kassabovA s, kassabovB s] (2 * s) (gen_top hs)
    (U ρ) (U_mul ρ) (U_one ρ) (U_adj ρ)
    (fun a => E 0 2 (by decide) a.1 * E 1 2 (by decide) a.2)
    (by show E _ _ _ 0 * E _ _ _ 0 = 1; rw [E_zero, E_zero, mul_one])
    (fun a b => c3_add a.1 a.2 b.1 b.2)
    (E 0 1 (by decide)) (E 1 0 (by decide)) (fun r a => c3_u r a.1 a.2) (fun r a => c3_l r a.1 a.2)
    v ε hε ?_ ?_ ?_ ?_ (r₁, r₂)
  · show ‖U ρ (E _ _ _ 1 * E _ _ _ 0) v - v‖ ≤ ε
    rw [E_zero, mul_one]; exact hv 1
  · show ‖U ρ (E _ _ _ 0 * E _ _ _ 1) v - v‖ ≤ ε
    rw [E_zero, one_mul]; exact hv 3
  · rintro (_ | j)
    · exact hv 0
    · fin_cases j
      · exact hv 6
      · exact hv 10
  · rintro (_ | j)
    · exact hv 2
    · fin_cases j
      · exact hv 7
      · exact hv 11

theorem inst_c1 (r₁ r₂ : Ms s) :
    ‖U ρ (E 1 0 (by decide) r₁ * E 2 0 (by decide) r₂) v - v‖ ≤ 18 * ε := by
  refine relT_group (R := Ms s) two_Ms ![kassabovA s, kassabovB s] (2 * s) (gen_top hs)
    (U ρ) (U_mul ρ) (U_one ρ) (U_adj ρ)
    (fun a => E 1 0 (by decide) a.1 * E 2 0 (by decide) a.2)
    (by show E _ _ _ 0 * E _ _ _ 0 = 1; rw [E_zero, E_zero, mul_one])
    (fun a b => c1_add a.1 a.2 b.1 b.2)
    (E 1 2 (by decide)) (E 2 1 (by decide)) (fun r a => c1_u r a.1 a.2) (fun r a => c1_l r a.1 a.2)
    v ε hε ?_ ?_ ?_ ?_ (r₁, r₂)
  · show ‖U ρ (E _ _ _ 1 * E _ _ _ 0) v - v‖ ≤ ε
    rw [E_zero, mul_one]; exact hv 2
  · show ‖U ρ (E _ _ _ 0 * E _ _ _ 1) v - v‖ ≤ ε
    rw [E_zero, one_mul]; exact hv 4
  · rintro (_ | j)
    · exact hv 3
    · fin_cases j
      · exact hv 8
      · exact hv 12
  · rintro (_ | j)
    · exact hv 5
    · fin_cases j
      · exact hv 9
      · exact hv 13

theorem inst_r1 (r₁ r₂ : Ms s) :
    ‖U ρ (E 0 1 (by decide) r₁ * E 0 2 (by decide) r₂) v - v‖ ≤ 18 * ε := by
  refine relT_group (R := (Ms s)ᵐᵒᵖ) two_op
    ![MulOpposite.op (kassabovA s), MulOpposite.op (kassabovB s)] (2 * s) (gen_top_op hs)
    (U ρ) (U_mul ρ) (U_one ρ) (U_adj ρ)
    (fun a => E 0 1 (by decide) a.1.unop * E 0 2 (by decide) a.2.unop)
    (by show E _ _ _ 0 * E _ _ _ 0 = 1; rw [E_zero, E_zero, mul_one])
    (fun a b => r1_add a.1.unop a.2.unop b.1.unop b.2.unop)
    (fun r => E 2 1 (by decide) r.unop) (fun r => E 1 2 (by decide) r.unop)
    (fun r a => r1_u r.unop a.1.unop a.2.unop) (fun r a => r1_l r.unop a.1.unop a.2.unop)
    v ε hε ?_ ?_ ?_ ?_ (MulOpposite.op r₁, MulOpposite.op r₂)
  · show ‖U ρ (E _ _ _ 1 * E _ _ _ 0) v - v‖ ≤ ε
    rw [E_zero, mul_one]; exact hv 0
  · show ‖U ρ (E _ _ _ 0 * E _ _ _ 1) v - v‖ ≤ ε
    rw [E_zero, one_mul]; exact hv 1
  · rintro (_ | j)
    · exact hv 5
    · fin_cases j
      · exact hv 9
      · exact hv 13
  · rintro (_ | j)
    · exact hv 3
    · fin_cases j
      · exact hv 8
      · exact hv 12

theorem inst_r3 (r₁ r₂ : Ms s) :
    ‖U ρ (E 2 0 (by decide) r₁ * E 2 1 (by decide) r₂) v - v‖ ≤ 18 * ε := by
  refine relT_group (R := (Ms s)ᵐᵒᵖ) two_op
    ![MulOpposite.op (kassabovA s), MulOpposite.op (kassabovB s)] (2 * s) (gen_top_op hs)
    (U ρ) (U_mul ρ) (U_one ρ) (U_adj ρ)
    (fun a => E 2 0 (by decide) a.1.unop * E 2 1 (by decide) a.2.unop)
    (by show E _ _ _ 0 * E _ _ _ 0 = 1; rw [E_zero, E_zero, mul_one])
    (fun a b => r3_add a.1.unop a.2.unop b.1.unop b.2.unop)
    (fun r => E 1 0 (by decide) r.unop) (fun r => E 0 1 (by decide) r.unop)
    (fun r a => r3_u r.unop a.1.unop a.2.unop) (fun r a => r3_l r.unop a.1.unop a.2.unop)
    v ε hε ?_ ?_ ?_ ?_ (MulOpposite.op r₁, MulOpposite.op r₂)
  · show ‖U ρ (E _ _ _ 1 * E _ _ _ 0) v - v‖ ≤ ε
    rw [E_zero, mul_one]; exact hv 4
  · show ‖U ρ (E _ _ _ 0 * E _ _ _ 1) v - v‖ ≤ ε
    rw [E_zero, one_mul]; exact hv 5
  · rintro (_ | j)
    · exact hv 2
    · fin_cases j
      · exact hv 7
      · exact hv 11
  · rintro (_ | j)
    · exact hv 0
    · fin_cases j
      · exact hv 6
      · exact hv 10

end

end KasSL

open DepthOneQExp in
theorem solution (s : ℕ) (hs : 1 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ∀ i : Fin 14, ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (sigma s i) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ ε)
    (r₁ r₂ : Matrix (Fin s) (Fin s) (ZMod 2)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom ((show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 2 r₂, det_blockElem s (by decide) r₂⟩)) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ 18 * ε ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom ((show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₂, det_blockElem s (by decide) r₂⟩)) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ 18 * ε ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom ((show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 1 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 2 r₂, det_blockElem s (by decide) r₂⟩)) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ 18 * ε ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom ((show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r₁, det_blockElem s (by decide) r₁⟩) * (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 1 r₂, det_blockElem s (by decide) r₂⟩)) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ≤ 18 * ε :=
  ⟨KasSL.inst_c3 ρ hs v ε hε hv r₁ r₂, KasSL.inst_c1 ρ hs v ε hε hv r₁ r₂,
    KasSL.inst_r1 ρ hs v ε hε hv r₁ r₂, KasSL.inst_r3 ρ hs v ε hε hv r₁ r₂⟩
