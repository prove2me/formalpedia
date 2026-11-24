-- Prove2me | solution 1 for DepthOneQExp.root_subgroups_kazhdan
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T07:41:05.278841+00:00
-- url     : https://prove2.me/submissions/474356a9-f589-4498-9b9e-8c16b1f4ca83

import Mathlib
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
open KasF


namespace KasG

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- `X ⊥_ε Y`: all inner products between the two subspaces are `ε`-small -/
def Orth (X Y : Submodule ℂ V) (ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖

theorem orth_symm {X Y : Submodule ℂ V} {ε : ℝ} (h : Orth X Y ε) : Orth Y X ε := by
  intro y hy x hx
  rw [← inner_conj_symm, RCLike.norm_conj]
  have := h x hx y hy
  linarith [mul_comm ‖x‖ ‖y‖]

theorem orth_mono {X Y X' Y' : Submodule ℂ V} {ε : ℝ} (h : Orth X Y ε) (hX : X' ≤ X) (hY : Y' ≤ Y) :
    Orth X' Y' ε := fun x hx y hy => h x (hX hx) y (hY hy)

theorem norm_inner_self' (x : V) : ‖⟪x, x⟫_ℂ‖ = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]

theorem proj_norm_sq (K : Submodule ℂ V) (v : V) :
    ‖v‖ ^ 2 = ‖K.starProjection v‖ ^ 2 + ‖v - K.starProjection v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (K.starProjection v)
    (v - K.starProjection v) (by
      rw [← inner_conj_symm]
      rw [Submodule.starProjection_inner_eq_zero v _ (K.starProjection_apply_mem v)]
      simp)
  rw [add_sub_cancel] at h
  nlinarith [h]

theorem inner_proj (K : Submodule ℂ V) (v : V) : ⟪K.starProjection v, v⟫_ℂ =
    ⟪K.starProjection v, K.starProjection v⟫_ℂ := by
  have h1 : ⟪K.starProjection v, v - K.starProjection v⟫_ℂ = 0 := by
    rw [← inner_conj_symm, Submodule.starProjection_inner_eq_zero v _ (K.starProjection_apply_mem v)]
    simp
  rw [inner_sub_right, sub_eq_zero] at h1
  exact h1

/-- the projection onto `Y` of a vector of `X` is short -/
theorem proj_short {X Y : Submodule ℂ V} {ε : ℝ} (h : Orth X Y ε) (hε : 0 ≤ ε) {x : V} (hx : x ∈ X) :
    ‖Y.starProjection x‖ ≤ ε * ‖x‖ := by
  have h1 := h x hx _ (Y.starProjection_apply_mem x)
  rw [← inner_conj_symm, RCLike.norm_conj, inner_proj, norm_inner_self'] at h1
  by_cases h0 : ‖Y.starProjection x‖ = 0
  · rw [h0]; positivity
  · have hp : 0 < ‖Y.starProjection x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem proj_self_adj (K : Submodule ℂ V) (a b : V) :
    ⟪K.starProjection a, b⟫_ℂ = ⟪a, K.starProjection b⟫_ℂ := by
  exact Submodule.inner_starProjection_left_eq_right K a b

theorem proj_orth_zero (K : Submodule ℂ V) {b : V} (hb : b ∈ Kᗮ) : K.starProjection b = 0 := by
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero K.zero_mem fun w hw => by
    rw [sub_zero]; exact Submodule.inner_left_of_mem_orthogonal hw hb

/-- sharp: complements of `ε`-orthogonal subspaces spanning `U` are `ε`-orthogonal in `U` -/
theorem orth_compl {X Y U : Submodule ℂ V} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : Orth X Y ε)
    (hU : U ≤ X ⊔ Y) : Orth (U ⊓ Xᗮ) (U ⊓ Yᗮ) ε := by
  intro a ha b hb
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hU hb.1)
  have hPb : Y.starProjection b = 0 := proj_orth_zero Y hb.2
  have hy' : y = -Y.starProjection x := by
    have : Y.starProjection (x + y) = Y.starProjection x + y := by
      rw [map_add, (Submodule.starProjection_eq_self_iff).2 hy]
    rw [hxy, hPb] at this
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact this.symm
  have hb' : b = x - Y.starProjection x := by rw [← hxy, hy']; abel
  have hbx : ⟪b, x⟫_ℂ = ⟪b, b⟫_ℂ := by
    have : ⟪b, Y.starProjection x⟫_ℂ = 0 := by
      rw [← proj_self_adj, hPb, inner_zero_left]
    calc ⟪b, x⟫_ℂ = ⟪b, b + Y.starProjection x⟫_ℂ := by rw [hb']; congr 1; abel
      _ = ⟪b, b⟫_ℂ := by rw [inner_add_right, this, add_zero]
  have hnx : ‖x‖ ^ 2 = ‖b‖ ^ 2 + ‖Y.starProjection x‖ ^ 2 := by
    rw [hb', proj_norm_sq Y x]; ring
  have hPYx := proj_short h hε hx
  have hab : ⟪a, b⟫_ℂ = ⟪a, b - X.starProjection b⟫_ℂ := by
    have : ⟪a, X.starProjection b⟫_ℂ = 0 := by
      rw [← proj_self_adj, proj_orth_zero X ha.2, inner_zero_left]
    rw [inner_sub_right, this, sub_zero]
  have hPXb : ‖b‖ ^ 2 ≤ ‖X.starProjection b‖ * ‖x‖ := by
    have : ⟪X.starProjection b, x⟫_ℂ = ⟪b, b⟫_ℂ := by
      rw [proj_self_adj, (Submodule.starProjection_eq_self_iff).2 hx, hbx]
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (X.starProjection b) x
    rw [this, norm_inner_self'] at h2
    exact h2
  have hres : ‖b - X.starProjection b‖ ^ 2 ≤ ε ^ 2 * ‖b‖ ^ 2 := by
    have hsplit := proj_norm_sq X b
    by_cases hx0 : ‖x‖ = 0
    · have : ‖b‖ = 0 := by
        have : ‖b‖ ^ 2 ≤ 0 := by rw [hx0, mul_zero] at hPXb; exact hPXb
        nlinarith [norm_nonneg b]
      have hb0 : b = 0 := norm_eq_zero.1 this
      rw [hb0]; simp
    · have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
      have h1 : (1 - ε ^ 2) * ‖x‖ ^ 2 ≤ ‖b‖ ^ 2 := by nlinarith [norm_nonneg (Y.starProjection x)]
      have h2 : ‖b‖ ^ 2 * ‖b‖ ^ 2 ≤ ‖X.starProjection b‖ ^ 2 * ‖x‖ ^ 2 := by
        have := mul_le_mul hPXb hPXb (by positivity) (by positivity)
        nlinarith
      have h3 : (1 - ε ^ 2) * ‖b‖ ^ 2 ≤ ‖X.starProjection b‖ ^ 2 := by
        by_contra hc
        push Not at hc
        have hε2 : 0 ≤ 1 - ε ^ 2 := by nlinarith
        have : ‖b‖ ^ 2 * ‖b‖ ^ 2 < ‖b‖ ^ 2 * ‖b‖ ^ 2 := by
          calc ‖b‖ ^ 2 * ‖b‖ ^ 2 ≤ ‖X.starProjection b‖ ^ 2 * ‖x‖ ^ 2 := h2
            _ < (1 - ε ^ 2) * ‖b‖ ^ 2 * ‖x‖ ^ 2 := by
                exact mul_lt_mul_of_pos_right hc (by positivity)
            _ ≤ ‖b‖ ^ 2 * ‖b‖ ^ 2 := by nlinarith
        exact lt_irrefl _ this
      nlinarith
  rw [hab]
  refine (norm_inner_le_norm (𝕜 := ℂ) a _).trans ?_
  have : ‖b - X.starProjection b‖ ≤ ε * ‖b‖ := by
    have := pow_le_pow_left₀ (norm_nonneg _) (le_refl ‖b - X.starProjection b‖) 2
    rw [← mul_pow] at hres
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hres
  nlinarith [norm_nonneg a]

theorem norm_add_sq_ge {x y : V} {ε : ℝ} (hxy : ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖) (hε0 : 0 ≤ ε) :
    (1 - ε) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖x + y‖ ^ 2 := by
  rw [@norm_add_sq ℂ]
  have h1 : -(ε * ‖x‖ * ‖y‖) ≤ RCLike.re ⟪x, y⟫_ℂ :=
    neg_le_of_abs_le ((RCLike.abs_re_le_norm _).trans hxy)
  nlinarith [mul_nonneg hε0 (sq_nonneg (‖x‖ - ‖y‖)), norm_nonneg x, norm_nonneg y]

/-- `(X + Y) ⊥ Z` from pairwise orthogonality -/
theorem orth_sup {X Y Z : Submodule ℂ V} {ε e0 : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (he0 : 0 ≤ e0)
    (he : 2 * ε ^ 2 ≤ e0 ^ 2 * (1 - ε))
    (hXY : Orth X Y ε) (hXZ : Orth X Z ε) (hYZ : Orth Y Z ε) : Orth (X ⊔ Y) Z e0 := by
  intro u hu z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hu
  have h1 : ‖⟪x + y, z⟫_ℂ‖ ≤ ε * (‖x‖ + ‖y‖) * ‖z‖ := by
    rw [inner_add_left]
    refine (norm_add_le _ _).trans ?_
    have := hXZ x hx z hz; have := hYZ y hy z hz; nlinarith
  have h2 := norm_add_sq_ge (hXY x hx y hy) hε
  have h3 : (ε * (‖x‖ + ‖y‖) * ‖z‖) ^ 2 ≤ (e0 * ‖x + y‖ * ‖z‖) ^ 2 := by
    have : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    have h4 : ε ^ 2 * (‖x‖ + ‖y‖) ^ 2 ≤ e0 ^ 2 * ‖x + y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left this (sq_nonneg ε)
      have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg e0)
      nlinarith [sq_nonneg (‖x‖ ^ 2 + ‖y‖ ^ 2)]
    have := mul_le_mul_of_nonneg_right h4 (sq_nonneg ‖z‖)
    nlinarith
  exact h1.trans ((pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h3)

/-- Kazhdanprep: a vector is far from one of two almost orthogonal subspaces -/
theorem kazhdanprep {U1 U2 : Submodule ℂ V} {η : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) (h : Orth U1 U2 η)
    (v : V) : (1 - η) / 2 * ‖v‖ ^ 2 ≤ ‖v - U1.starProjection v‖ ^ 2 ∨
      (1 - η) / 2 * ‖v‖ ^ 2 ≤ ‖v - U2.starProjection v‖ ^ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  set a1 := U1.starProjection v
  set a2 := U2.starProjection v
  have e1 := proj_norm_sq U1 v
  have e2 := proj_norm_sq U2 v
  have hre : ‖a1‖ ^ 2 + ‖a2‖ ^ 2 = RCLike.re ⟪a1 + a2, v⟫_ℂ := by
    rw [inner_add_left, map_add, inner_proj, inner_proj, inner_self_eq_norm_sq,
      inner_self_eq_norm_sq]
  have hle : RCLike.re ⟪a1 + a2, v⟫_ℂ ≤ ‖a1 + a2‖ * ‖v‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hsum : ‖a1 + a2‖ ^ 2 ≤ (1 + η) * (‖a1‖ ^ 2 + ‖a2‖ ^ 2) := by
    rw [@norm_add_sq ℂ]
    have := (RCLike.re_le_norm _).trans (h a1 (U1.starProjection_apply_mem v) a2
      (U2.starProjection_apply_mem v))
    nlinarith [sq_nonneg (‖a1‖ - ‖a2‖), norm_nonneg a1, norm_nonneg a2]
  set S := ‖a1‖ ^ 2 + ‖a2‖ ^ 2
  have hS : (1 + η) * ‖v‖ ^ 2 < S := by linarith
  have hS0 : 0 ≤ S := by positivity
  have : S ^ 2 ≤ (1 + η) * S * ‖v‖ ^ 2 := by
    have h6 : S ≤ ‖a1 + a2‖ * ‖v‖ := hre ▸ hle
    have h7 : S ^ 2 ≤ ‖a1 + a2‖ ^ 2 * ‖v‖ ^ 2 := by
      have := mul_le_mul h6 h6 hS0 (by positivity); nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hsum (sq_nonneg ‖v‖)]
  have hSpos : 0 < S := lt_of_le_of_lt (by positivity) hS
  have : S ≤ (1 + η) * ‖v‖ ^ 2 := by
    have h8 : S * S ≤ ((1 + η) * ‖v‖ ^ 2) * S := by nlinarith
    exact le_of_mul_le_mul_right h8 hSpos
  linarith

theorem proj_eq_self {K : Submodule ℂ V} {x : V} (hx : x ∈ K) : K.starProjection x = x :=
  (Submodule.starProjection_eq_self_iff).2 hx

/-- `w - P_K w ⊥ K` -/
theorem sub_proj_mem (K : Submodule ℂ V) (w : V) : w - K.starProjection w ∈ Kᗮ :=
  Submodule.sub_starProjection_mem_orthogonal w

/-- complement inside `W`: if `K ≤ W` and `w ∈ W` is orthogonal to `W ⊓ Kᗮ` then `w ∈ K` -/
theorem mem_of_perp {K W : Submodule ℂ V} (hKW : K ≤ W) {w : V} (hw : w ∈ W)
    (hperp : ∀ z ∈ W ⊓ Kᗮ, ⟪z, w⟫_ℂ = 0) : w ∈ K := by
  set r := w - K.starProjection w
  have hr : r ∈ W ⊓ Kᗮ := ⟨W.sub_mem hw (hKW (K.starProjection_apply_mem w)), sub_proj_mem K w⟩
  have h1 : ⟪r, w⟫_ℂ = 0 := hperp r hr
  have h2 : ⟪r, K.starProjection w⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (K.starProjection_apply_mem w) hr.2
  have h3 : ⟪r, r⟫_ℂ = 0 := by
    rw [show r = w - K.starProjection w from rfl, inner_sub_right]
    rw [show w - K.starProjection w = r from rfl, h1, h2, sub_zero]
  have : r = 0 := inner_self_eq_zero.1 h3
  rw [← proj_eq_self (K := K) (x := w) ?_]
  · exact K.starProjection_apply_mem w
  · have := sub_eq_zero.1 this
    rw [this]; exact K.starProjection_apply_mem w

/-- if `K ≤ W` and nothing in `W` is orthogonal to `K`, then `W ≤ K` -/
theorem le_of_perp_bot {K W : Submodule ℂ V} (hKW : K ≤ W)
    (h : ∀ w ∈ W, (∀ k ∈ K, ⟪k, w⟫_ℂ = 0) → w = 0) : W ≤ K := by
  intro w hw
  set r := w - K.starProjection w
  have hr : r ∈ W := W.sub_mem hw (hKW (K.starProjection_apply_mem w))
  have hr0 : r = 0 := h r hr (fun k hk => Submodule.inner_right_of_mem_orthogonal hk (sub_proj_mem K w))
  have := sub_eq_zero.1 hr0
  rw [this]; exact K.starProjection_apply_mem w

/-- the pair step of Ershov–Jaikin-Zapirain's Proposition 3.2 -/
theorem pair_step {Fa Fb A B V0 : Submodule ℂ V} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hA : A ≤ Fa) (hB : B ≤ Fb) (hV0 : V0 = A ⊔ B ⊔ (Fa ⊓ Fb))
    (h : Orth (Fa ⊓ (Fa ⊓ Fb)ᗮ) (Fb ⊓ (Fa ⊓ Fb)ᗮ) ε) :
    Orth (V0 ⊓ Aᗮ ⊓ (Fa ⊓ Fb)ᗮ) (V0 ⊓ Bᗮ ⊓ (Fa ⊓ Fb)ᗮ) ε ∧
      V0 ⊓ (Fa ⊓ Fb)ᗮ ≤ (V0 ⊓ Aᗮ ⊓ (Fa ⊓ Fb)ᗮ) ⊔ (V0 ⊓ Bᗮ ⊓ (Fa ⊓ Fb)ᗮ) := by
  set C := Fa ⊓ Fb
  set P : V →L[ℂ] V := Cᗮ.starProjection
  have hP : ∀ x, P x = x - C.starProjection x := by
    intro x
    have := Submodule.starProjection_orthogonal' (U := C)
    show (Cᗮ).starProjection x = _
    rw [Submodule.starProjection_orthogonal]
    simp
  have hCV0 : C ≤ V0 := hV0 ▸ le_sup_right
  have hAV0 : A ≤ V0 := hV0 ▸ (le_sup_left.trans le_sup_left)
  have hBV0 : B ≤ V0 := hV0 ▸ (le_sup_right.trans le_sup_left)
  set X : Submodule ℂ V := A.map (P : V →ₗ[ℂ] V)
  set Y : Submodule ℂ V := B.map (P : V →ₗ[ℂ] V)
  have hX : X ≤ Fa ⊓ Cᗮ := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · show P a ∈ Fa
      rw [hP]
      exact Fa.sub_mem (hA ha) ((inf_le_left : C ≤ Fa) (C.starProjection_apply_mem a))
    · exact Cᗮ.starProjection_apply_mem a
  have hY : Y ≤ Fb ⊓ Cᗮ := by
    rintro _ ⟨b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · show P b ∈ Fb
      rw [hP]
      exact Fb.sub_mem (hB hb) ((inf_le_right : C ≤ Fb) (C.starProjection_apply_mem b))
    · exact Cᗮ.starProjection_apply_mem b
  have hXY : Orth X Y ε := orth_mono h hX hY
  set W := V0 ⊓ Cᗮ
  have hPV0 : ∀ x ∈ V0, P x ∈ W := fun x hx =>
    ⟨by rw [hP]; exact V0.sub_mem hx (hCV0 (C.starProjection_apply_mem x)),
      Cᗮ.starProjection_apply_mem x⟩
  have hXW : X ≤ W := by rintro _ ⟨a, ha, rfl⟩; exact hPV0 a (hAV0 ha)
  have hYW : Y ≤ W := by rintro _ ⟨b, hb, rfl⟩; exact hPV0 b (hBV0 hb)
  have hWXY : W ≤ X ⊔ Y := by
    intro w hw
    have hw' := hw.1
    rw [hV0] at hw'
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.1 hw'
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hab
    have hPw : P (a + b + c) = a + b + c := proj_eq_self hw.2
    have hPc : P c = 0 := by rw [hP, proj_eq_self hc, sub_self]
    rw [← hPw, map_add, map_add, hPc, add_zero]
    exact Submodule.add_mem_sup ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have hZ1 : V0 ⊓ Aᗮ ⊓ Cᗮ ≤ W ⊓ Xᗮ := by
    rintro z ⟨⟨hz0, hzA⟩, hzC⟩
    refine ⟨⟨hz0, hzC⟩, ?_⟩
    show z ∈ Xᗮ
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨a, ha, rfl⟩
    show ⟪P a, z⟫_ℂ = 0
    rw [hP, inner_sub_left, Submodule.inner_right_of_mem_orthogonal ha hzA,
      Submodule.inner_right_of_mem_orthogonal (C.starProjection_apply_mem a) hzC, sub_zero]
  have hZ2 : V0 ⊓ Bᗮ ⊓ Cᗮ ≤ W ⊓ Yᗮ := by
    rintro z ⟨⟨hz0, hzB⟩, hzC⟩
    refine ⟨⟨hz0, hzC⟩, ?_⟩
    show z ∈ Yᗮ
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨b, hb, rfl⟩
    show ⟪P b, z⟫_ℂ = 0
    rw [hP, inner_sub_left, Submodule.inner_right_of_mem_orthogonal hb hzB,
      Submodule.inner_right_of_mem_orthogonal (C.starProjection_apply_mem b) hzC, sub_zero]
  refine ⟨orth_mono (orth_compl hε hε1.le hXY hWXY) hZ1 hZ2, ?_⟩
  -- covering
  refine le_of_perp_bot (sup_le (fun z hz => ⟨hz.1.1, hz.2⟩) (fun z hz => ⟨hz.1.1, hz.2⟩)) ?_
  intro w hw hperp
  -- `w ∈ X` and `w ∈ Y`
  have hwX : w ∈ X := by
    refine mem_of_perp hXW hw fun z hz => ?_
    have hzZ : z ∈ V0 ⊓ Aᗮ ⊓ Cᗮ := by
      refine ⟨⟨hz.1.1, ?_⟩, hz.1.2⟩
      show z ∈ Aᗮ
      rw [Submodule.mem_orthogonal]
      intro a ha
      have h1 : ⟪P a, z⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (show P a ∈ X from ⟨a, ha, rfl⟩) hz.2
      have h2 : ⟪C.starProjection a, z⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (C.starProjection_apply_mem a) hz.1.2
      rw [hP, inner_sub_left, h2, sub_zero] at h1
      exact h1
    exact hperp z (Submodule.mem_sup_left hzZ)
  have hwY : w ∈ Y := by
    refine mem_of_perp hYW hw fun z hz => ?_
    have hzZ : z ∈ V0 ⊓ Bᗮ ⊓ Cᗮ := by
      refine ⟨⟨hz.1.1, ?_⟩, hz.1.2⟩
      show z ∈ Bᗮ
      rw [Submodule.mem_orthogonal]
      intro b hb
      have h1 : ⟪P b, z⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (show P b ∈ Y from ⟨b, hb, rfl⟩) hz.2
      have h2 : ⟪C.starProjection b, z⟫_ℂ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (C.starProjection_apply_mem b) hz.1.2
      rw [hP, inner_sub_left, h2, sub_zero] at h1
      exact h1
    exact hperp z (Submodule.mem_sup_right hzZ)
  have h1 := hXY w hwX w hwY
  rw [norm_inner_self'] at h1
  have : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)

/-- Ershov–Jaikin-Zapirain, Proposition 3.2 (finite-dimensional, explicit constants) -/
theorem ejz {F1 F2 F3 : Submodule ℂ V} {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ^ 2 ≤ 1 / 8)
    (h12 : Orth (F1 ⊓ (F1 ⊓ F2)ᗮ) (F2 ⊓ (F1 ⊓ F2)ᗮ) ε)
    (h13 : Orth (F1 ⊓ (F1 ⊓ F3)ᗮ) (F3 ⊓ (F1 ⊓ F3)ᗮ) ε)
    (h23 : Orth (F2 ⊓ (F2 ⊓ F3)ᗮ) (F3 ⊓ (F2 ⊓ F3)ᗮ) ε)
    (htriple : ∀ x, x ∈ F1 → x ∈ F2 → x ∈ F3 → x = 0) :
    Orth (F1 ⊓ F2) (F1 ⊓ F3) 0.63 := by
  have hε1 : ε < 1 := by nlinarith
  have hεs : ε ≤ 0.36 := by nlinarith
  set V1 := F2 ⊓ F3
  set V2 := F1 ⊓ F3
  set V3 := F1 ⊓ F2
  set V0 := V1 ⊔ V2 ⊔ V3 with hV0
  set Z1 := V0 ⊓ V2ᗮ ⊓ V3ᗮ
  set Z2 := V0 ⊓ V1ᗮ ⊓ V3ᗮ
  set Z3 := V0 ⊓ V1ᗮ ⊓ V2ᗮ
  -- pair (1,2)
  obtain ⟨o12, cov⟩ := pair_step (Fa := F1) (Fb := F2) (A := V2) (B := V1) (V0 := V0) hε hε1
    inf_le_left inf_le_left (by rw [hV0]; simp only [V3]; ac_rfl) h12
  -- pair (1,3)
  obtain ⟨o13, -⟩ := pair_step (Fa := F1) (Fb := F3) (A := V3) (B := V1) (V0 := V0) hε hε1
    inf_le_left inf_le_right (by rw [hV0]; simp only [V2]; ac_rfl) h13
  -- pair (2,3)
  obtain ⟨o23, -⟩ := pair_step (Fa := F2) (Fb := F3) (A := V3) (B := V2) (V0 := V0) hε hε1
    inf_le_right inf_le_right (by rw [hV0]; simp only [V1]; ac_rfl) h23
  have e13 : V0 ⊓ V3ᗮ ⊓ V2ᗮ = Z1 := by simp only [Z1]; ac_rfl
  have e23a : V0 ⊓ V3ᗮ ⊓ V1ᗮ = Z2 := by simp only [Z2]; ac_rfl
  have e23b : V0 ⊓ V2ᗮ ⊓ V1ᗮ = Z3 := by simp only [Z3]; ac_rfl
  have o13' : Orth Z1 Z3 ε := by
    have := o13; simp only [show F1 ⊓ F3 = V2 from rfl] at this; rwa [e13] at this
  have o23' : Orth Z2 Z3 ε := by
    have := o23; simp only [show F2 ⊓ F3 = V1 from rfl] at this; rwa [e23a, e23b] at this
  have hsup := orth_sup (X := Z1) (Y := Z2) (Z := Z3) (e0 := 0.63) hε hε1 (by norm_num)
    (by nlinarith) o12 o13' o23'
  have hW : Orth (V0 ⊓ V3ᗮ) Z3 0.63 := orth_mono hsup cov le_rfl
  -- `V0 ≤ (V0 ⊓ V3ᗮ) ⊔ Z3`
  have hcov2 : V0 ≤ (V0 ⊓ V3ᗮ) ⊔ Z3 := by
    refine le_of_perp_bot (sup_le inf_le_left (fun z hz => hz.1.1)) ?_
    intro w hw hperp
    have hw3 : w ∈ V3 := mem_of_perp (le_sup_right : V3 ≤ V0) hw fun z hz =>
      hperp z (Submodule.mem_sup_left hz)
    have hw12 : w ∈ V1 ⊔ V2 := by
      refine mem_of_perp (le_sup_left : V1 ⊔ V2 ≤ V0) hw fun z hz => ?_
      refine hperp z (Submodule.mem_sup_right ⟨⟨hz.1, ?_⟩, ?_⟩)
      · rw [← Submodule.inf_orthogonal] at hz
        exact hz.2.1
      · rw [← Submodule.inf_orthogonal] at hz
        exact hz.2.2
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hw12
    have hv2F2 : v2 ∈ F2 := by
      have : v2 = (v1 + v2) - v1 := by abel
      rw [this]; exact F2.sub_mem hw3.2 hv1.1
    have hv2z : v2 = 0 := htriple v2 hv2.1 hv2F2 hv2.2
    rw [hv2z, add_zero] at hw3 ⊢
    exact htriple v1 hw3.1 hv1.1 hv1.2
  have hfin := orth_compl (X := V0 ⊓ V3ᗮ) (Y := Z3) (U := V0) (by norm_num) (by norm_num) hW hcov2
  refine orth_mono hfin ?_ ?_
  · intro x hx
    refine ⟨(le_sup_right : V3 ≤ V0) hx, ?_⟩
    show x ∈ (V0 ⊓ V3ᗮ)ᗮ
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact Submodule.inner_left_of_mem_orthogonal hx hz.2
  · intro x hx
    refine ⟨(le_sup_right.trans le_sup_left : V2 ≤ V0) hx, ?_⟩
    show x ∈ Z3ᗮ
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact Submodule.inner_left_of_mem_orthogonal hx hz.2

theorem dist_proj_le (K : Submodule ℂ V) (b k : V) (hk : k ∈ K) :
    ‖b - K.starProjection b‖ ≤ ‖b - k‖ := by
  have h1 : ⟪b - K.starProjection b, K.starProjection b - k⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero b _ (K.sub_mem (K.starProjection_apply_mem b) hk)
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _ h1
  rw [show b - K.starProjection b + (K.starProjection b - k) = b - k by abel] at h2
  have : ‖b - K.starProjection b‖ ^ 2 ≤ ‖b - k‖ ^ 2 := by nlinarith [sq_nonneg ‖K.starProjection b - k‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 this

/-- nested projections: if `U ≤ F` and `b ⊥ U`, then `P_F b ⊥ U` -/
theorem proj_perp_of_le {U F : Submodule ℂ V} (hUF : U ≤ F) {b : V} (hb : b ∈ Uᗮ) :
    F.starProjection b ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  have : ⟪u, F.starProjection b⟫_ℂ = ⟪F.starProjection u, b⟫_ℂ := (proj_self_adj F u b).symm
  rw [this, proj_eq_self (hUF hu)]
  exact Submodule.inner_right_of_mem_orthogonal hu hb

/-- one pair: from `v`, far from `U = Fa ⊓ Fb`, get a far subspace among `Fa`, `Fb` -/
theorem pair_far {Fa Fb : Submodule ℂ V} {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1)
    (h : Orth (Fa ⊓ (Fa ⊓ Fb)ᗮ) (Fb ⊓ (Fa ⊓ Fb)ᗮ) ε) (v : V) :
    (1 - ε) / 2 * ‖v - (Fa ⊓ Fb).starProjection v‖ ^ 2 ≤ ‖v - Fa.starProjection v‖ ^ 2 ∨
    (1 - ε) / 2 * ‖v - (Fa ⊓ Fb).starProjection v‖ ^ 2 ≤ ‖v - Fb.starProjection v‖ ^ 2 := by
  set U := Fa ⊓ Fb
  set b := v - U.starProjection v
  have hb : b ∈ Uᗮ := sub_proj_mem U v
  have key : ∀ F : Submodule ℂ V, U ≤ F →
      ‖b - (F ⊓ Uᗮ).starProjection b‖ ≤ ‖v - F.starProjection v‖ := by
    intro F hUF
    have e1 : v - F.starProjection v = b - F.starProjection b := by
      have : F.starProjection (U.starProjection v) = U.starProjection v :=
        proj_eq_self (hUF (U.starProjection_apply_mem v))
      simp only [b, map_sub, this]; abel
    rw [e1]
    exact dist_proj_le _ b _ ⟨F.starProjection_apply_mem b, proj_perp_of_le hUF hb⟩
  rcases kazhdanprep hε hε1 h b with h1 | h1
  · left
    exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) (key Fa inf_le_left) 2)
  · right
    exact h1.trans (pow_le_pow_left₀ (norm_nonneg _) (key Fb inf_le_right) 2)

/-- **three subspaces**: under the hypotheses of `ejz`, every vector is far from one of the three
subspaces -/
theorem three_far {F1 F2 F3 : Submodule ℂ V} {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε ^ 2 ≤ 1 / 8)
    (h12 : Orth (F1 ⊓ (F1 ⊓ F2)ᗮ) (F2 ⊓ (F1 ⊓ F2)ᗮ) ε)
    (h13 : Orth (F1 ⊓ (F1 ⊓ F3)ᗮ) (F3 ⊓ (F1 ⊓ F3)ᗮ) ε)
    (h23 : Orth (F2 ⊓ (F2 ⊓ F3)ᗮ) (F3 ⊓ (F2 ⊓ F3)ᗮ) ε)
    (htriple : ∀ x, x ∈ F1 → x ∈ F2 → x ∈ F3 → x = 0) (v : V) :
    1 / 20 * ‖v‖ ^ 2 ≤ ‖v - F1.starProjection v‖ ^ 2 ∨
    1 / 20 * ‖v‖ ^ 2 ≤ ‖v - F2.starProjection v‖ ^ 2 ∨
    1 / 20 * ‖v‖ ^ 2 ≤ ‖v - F3.starProjection v‖ ^ 2 := by
  have hε1 : ε < 1 := by nlinarith
  have hεs : ε ≤ 0.36 := by nlinarith
  have hE := ejz hε hε2 h12 h13 h23 htriple
  have hv0 := sq_nonneg ‖v‖
  rcases kazhdanprep (by norm_num) (by norm_num) hE v with hk | hk
  · rcases pair_far hε hε1 h12 v with h | h
    · left; nlinarith
    · right; left; nlinarith
  · rcases pair_far hε hε1 h13 v with h | h
    · left; nlinarith
    · right; right; nlinarith

end KasG


open KasG

namespace KasH

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- the common fixed vectors of a family of operators -/
def fixSub {ι : Type} (T : ι → (V →L[ℂ] V)) : Submodule ℂ V where
  carrier := {v | ∀ i, T i v = v}
  add_mem' {a b} ha hb i := by rw [map_add, ha i, hb i]
  zero_mem' i := map_zero _
  smul_mem' c v hv i := by rw [map_smul, hv i]

theorem mem_fixSub {ι : Type} (T : ι → (V →L[ℂ] V)) (v : V) : v ∈ fixSub T ↔ ∀ i, T i v = v :=
  Iff.rfl

variable {R : Type} [Ring R] [Fintype R] [DecidableEq R]

/-- a unitary representation of `(R, +)` -/
structure Hom (R V : Type) [Ring R] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] where
  T : R → (V →L[ℂ] V)
  map_zero : T 0 = 1
  map_add : ∀ a b, T (a + b) = T a * T b
  adj : ∀ a, ContinuousLinearMap.adjoint (T a) = T (-a)

def Hom.toURep (X : Hom R V) : URep R V := ⟨X.T, X.map_zero, X.map_add, X.adj⟩

theorem Hom.iso (X : Hom R V) (a : R) (w : V) : ‖X.T a w‖ = ‖w‖ := by
  have h : ⟪X.T a w, X.T a w⟫_ℂ = ⟪w, w⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply, X.adj,
      ← X.map_add, neg_add_cancel, X.map_zero, ContinuousLinearMap.one_apply]
  have h2 : ‖X.T a w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- the average over `X`: the projection onto the `X`-fixed vectors -/
noncomputable def avg (X : Hom R V) : V →L[ℂ] V := proj X.toURep 1

theorem avg_eq (X : Hom R V) : avg X = (1 / (Fintype.card R : ℂ)) • ∑ a, X.T a := by
  simp [avg, proj, Hom.toURep]

theorem avg_mem (X : Hom R V) (w : V) : avg X w ∈ fixSub X.T := by
  intro a
  have := W_mul_proj X.toURep a 1
  simp only [AddChar.one_apply, one_smul] at this
  show X.T a (avg X w) = avg X w
  rw [avg, ← ContinuousLinearMap.mul_apply]
  exact congrArg (fun T => T w) this

theorem avg_fix (X : Hom R V) {w : V} (hw : w ∈ fixSub X.T) : avg X w = w := by
  rw [avg_eq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun a _ => hw a), Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem avg_adj (X : Hom R V) : ContinuousLinearMap.adjoint (avg X) = avg X := proj_adj _ _

section Heis
variable (X Y Z : Hom R V)

theorem Hom.neg_mul (X : Hom R V) (a : R) : X.T (-a) * X.T a = 1 := by
  rw [← X.map_add, neg_add_cancel, X.map_zero]

theorem comm_proj (hzx : ∀ c a, Z.T c * X.T a = X.T a * Z.T c) (ψ : AddChar R ℂ) (a : R) :
    X.T a * proj Z.toURep ψ = proj Z.toURep ψ * X.T a := by
  unfold proj
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  exact (hzx c a).symm

theorem proj_fix (hzx : ∀ c a, Z.T c * X.T a = X.T a * Z.T c) (ψ : AddChar R ℂ) {u : V}
    (hu : u ∈ fixSub X.T) : proj Z.toURep ψ u ∈ fixSub X.T := by
  intro a
  rw [← ContinuousLinearMap.mul_apply, comm_proj X Z hzx, ContinuousLinearMap.mul_apply, hu a]

theorem Z_on_proj (ψ : AddChar R ℂ) (c : R) (w : V) :
    Z.T c (proj Z.toURep ψ w) = ψ c • proj Z.toURep ψ w := by
  have := W_mul_proj Z.toURep c ψ
  exact congrArg (fun T => T w) this

/-- the key commutation `Y(-b) X(a) = X(a) Y(-b) Z(ab)` -/
theorem rel' (hrel : ∀ a b, X.T a * Y.T b = Y.T b * X.T a * Z.T (a * b))
    (hzy : ∀ c b, Z.T c * Y.T b = Y.T b * Z.T c) (a b : R) :
    Y.T (-b) * X.T a = X.T a * Y.T (-b) * Z.T (a * b) := by
  have h1 := hrel a (-b)
  -- multiply on the right by Z(a b) = Z(-(a(-b)))
  have h2 : Z.T (a * -b) * Z.T (a * b) = 1 := by
    rw [← Z.map_add, mul_neg, neg_add_cancel, Z.map_zero]
  calc Y.T (-b) * X.T a = Y.T (-b) * X.T a * (Z.T (a * -b) * Z.T (a * b)) := by rw [h2, mul_one]
    _ = (Y.T (-b) * X.T a * Z.T (a * -b)) * Z.T (a * b) := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = X.T a * Y.T (-b) * Z.T (a * b) := by rw [← h1]

end Heis

section Heis2
variable (X Y Z : Hom R V)
  (hrel : ∀ a b, X.T a * Y.T b = Y.T b * X.T a * Z.T (a * b))
  (hzx : ∀ c a, Z.T c * X.T a = X.T a * Z.T c) (hzy : ∀ c b, Z.T c * Y.T b = Y.T b * Z.T c)
include hrel hzx hzy

/-- on a `Z`-eigenspace with character `ψ`, `⟪X(a) w, w⟫ = 0` unless `ψ(aR) = 1` -/
theorem inner_X_zero (ψ : AddChar R ℂ) {w : V} (hw : w ∈ fixSub Y.T)
    (hwψ : ∀ c, Z.T c w = ψ c • w) (a : R) (ha : ∃ r, ψ (a * r) ≠ 1) :
    ⟪X.T a w, w⟫_ℂ = 0 := by
  obtain ⟨b, hb⟩ := ha
  have h1 : Y.T (-b) (X.T a w) = ψ (a * b) • X.T a w := by
    rw [← ContinuousLinearMap.mul_apply, rel' X Y Z hrel hzy a b, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.mul_apply, hwψ, map_smul, map_smul, hw (-b)]
  have h2 : ⟪X.T a w, w⟫_ℂ = ⟪Y.T (-b) (X.T a w), w⟫_ℂ := by
    rw [← Y.adj b, ContinuousLinearMap.adjoint_inner_left, hw b]
  rw [h1, inner_smul_left] at h2
  have h3 : (1 - (starRingEnd ℂ) (ψ (a * b))) * ⟪X.T a w, w⟫_ℂ = 0 := by
    rw [sub_mul, one_mul, ← h2, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exfalso; apply hb
    have : (starRingEnd ℂ) (ψ (a * b)) = 1 := by rw [sub_eq_zero] at h; exact h.symm
    rw [← RingHom.map_one (starRingEnd ℂ)] at this
    exact (starRingEnd ℂ).injective this
  · exact h

theorem avg_small (ψ : AddChar R ℂ) {w : V} (hw : w ∈ fixSub Y.T)
    (hwψ : ∀ c, Z.T c w = ψ c • w) (δ : ℝ)
    (hidx : ((Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1).card : ℝ) ≤ δ * Fintype.card R) :
    ‖avg X w‖ ^ 2 ≤ δ * ‖w‖ ^ 2 := by
  have hAA : avg X * avg X = avg X := by
    have := proj_mul_proj X.toURep 1 1; rw [if_pos rfl] at this; exact this
  have h1 : ‖avg X w‖ ^ 2 = RCLike.re ⟪avg X w, w⟫_ℂ := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← ContinuousLinearMap.adjoint_inner_right, avg_adj,
      ← ContinuousLinearMap.mul_apply, hAA, ← inner_re_symm (𝕜 := ℂ)]
  have h2 : ⟪avg X w, w⟫_ℂ = (1 / (Fintype.card R : ℂ)) *
      ∑ a ∈ (Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1), ⟪X.T a w, w⟫_ℂ := by
    rw [avg_eq, ContinuousLinearMap.smul_apply, inner_smul_left, ContinuousLinearMap.sum_apply,
      sum_inner, Finset.sum_filter]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with ha
      · rfl
      · push Not at ha
        exact inner_X_zero X Y Z hrel hzx hzy ψ hw hwψ a ha
  have h3 : ‖⟪avg X w, w⟫_ℂ‖ ≤ δ * ‖w‖ ^ 2 := by
    rw [h2, norm_mul, norm_div, norm_one, Complex.norm_natCast]
    have hc : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
    have hs : ‖∑ a ∈ (Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1), ⟪X.T a w, w⟫_ℂ‖ ≤
        ((Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1).card : ℝ) * ‖w‖ ^ 2 := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ a ∈ (Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1), ‖⟪X.T a w, w⟫_ℂ‖ ≤ ‖w‖ ^ 2 :=
        fun a _ => (norm_inner_le_norm _ _).trans (by rw [X.iso]; ring_nf; rfl)
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
    nlinarith [sq_nonneg ‖w‖]
  rw [h1]
  exact (RCLike.re_le_norm _).trans h3

/-- **Heisenberg orthogonality** -/
theorem heis_orth (δ : ℝ) (hδ : 0 ≤ δ)
    (hidx : ∀ ψ : AddChar R ℂ, ψ ≠ 1 →
      ((Finset.univ.filter fun a : R => ∀ r, ψ (a * r) = 1).card : ℝ) ≤ δ * Fintype.card R) :
    Orth (fixSub X.T ⊓ (fixSub X.T ⊓ fixSub Y.T)ᗮ) (fixSub Y.T ⊓ (fixSub X.T ⊓ fixSub Y.T)ᗮ)
      (Real.sqrt δ) := by
  intro u hu w hw
  set E := fun ψ : AddChar R ℂ => proj Z.toURep ψ
  have hEE : ∀ ψ, E ψ * E ψ = E ψ := fun ψ => by
    have := proj_mul_proj Z.toURep ψ ψ; rw [if_pos rfl] at this; exact this
  have hEadj : ∀ ψ, ContinuousLinearMap.adjoint (E ψ) = E ψ := fun ψ => proj_adj _ _
  have hdec : ⟪u, w⟫_ℂ = ∑ ψ, ⟪E ψ u, E ψ w⟫_ℂ := by
    have hu' : u = ∑ ψ, E ψ u := by
      rw [← ContinuousLinearMap.sum_apply, sum_proj, ContinuousLinearMap.one_apply]
    conv_lhs => rw [hu']
    rw [sum_inner]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    symm
    rw [← ContinuousLinearMap.adjoint_inner_left (E ψ), hEadj, ← ContinuousLinearMap.mul_apply, hEE]
  -- each term
  have hterm : ∀ ψ, ‖⟪E ψ u, E ψ w⟫_ℂ‖ ≤ Real.sqrt δ * (‖E ψ u‖ * ‖E ψ w‖) := by
    intro ψ
    set u' := E ψ u
    set w' := E ψ w
    have hu' : u' ∈ fixSub X.T := proj_fix X Z hzx ψ hu.1
    have hw' : w' ∈ fixSub Y.T := proj_fix Y Z hzy ψ hw.1
    have hZw : ∀ c, Z.T c w' = ψ c • w' := fun c => Z_on_proj Z ψ c w
    have hsw : ⟪u', w'⟫_ℂ = ⟪u', avg X w'⟫_ℂ := by
      rw [← avg_adj X, ContinuousLinearMap.adjoint_inner_right, avg_fix X hu']
    by_cases hψ : ψ = 1
    · -- the trivial character: the inner product vanishes
      have hY : avg X w' ∈ fixSub Y.T := by
        intro b
        rw [avg_eq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, map_smul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        have := rel' X Y Z hrel hzy a (-b)
        rw [neg_neg] at this
        rw [← ContinuousLinearMap.mul_apply, this, ContinuousLinearMap.mul_apply,
          ContinuousLinearMap.mul_apply, hZw, hψ, AddChar.one_apply, one_smul, hw' b]
      have hperp : avg X w' ∈ (fixSub X.T ⊓ fixSub Y.T)ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro k hk
        rw [← avg_adj X, ContinuousLinearMap.adjoint_inner_right, avg_fix X hk.1]
        show ⟪k, E ψ w⟫_ℂ = 0
        rw [← hEadj ψ, ContinuousLinearMap.adjoint_inner_right]
        exact Submodule.inner_right_of_mem_orthogonal
          (show E ψ k ∈ fixSub X.T ⊓ fixSub Y.T from ⟨proj_fix X Z hzx ψ hk.1, proj_fix Y Z hzy ψ hk.2⟩) hw.2
      have h0 : avg X w' = 0 := by
        have hmem : avg X w' ∈ fixSub X.T ⊓ fixSub Y.T := ⟨avg_mem X w', hY⟩
        exact (Submodule.mem_inf.1 ⟨hmem, hperp⟩ |> fun h =>
          inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h.1 h.2))
      rw [hsw, h0, inner_zero_right, norm_zero]
      positivity
    · rw [hsw]
      refine (norm_inner_le_norm _ _).trans ?_
      have h2 := avg_small X Y Z hrel hzx hzy ψ hw' hZw δ (hidx ψ hψ)
      have h3 : ‖avg X w'‖ ≤ Real.sqrt δ * ‖w'‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (avg X w')), ← Real.sqrt_sq (norm_nonneg w'),
          ← Real.sqrt_mul hδ]
        exact Real.sqrt_le_sqrt h2
      calc ‖u'‖ * ‖avg X w'‖ ≤ ‖u'‖ * (Real.sqrt δ * ‖w'‖) :=
            mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
        _ = Real.sqrt δ * (‖u'‖ * ‖w'‖) := by ring
  rw [hdec]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun ψ _ => hterm ψ).trans ?_)
  rw [← Finset.mul_sum]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun ψ => ‖E ψ u‖) (fun ψ => ‖E ψ w‖)
  have hu2 : Real.sqrt (∑ ψ, ‖E ψ u‖ ^ 2) = ‖u‖ := by
    rw [← norm_sq_eq_sum Z.toURep u, Real.sqrt_sq (norm_nonneg _)]
  have hw2 : Real.sqrt (∑ ψ, ‖E ψ w‖ ^ 2) = ‖w‖ := by
    rw [← norm_sq_eq_sum Z.toURep w, Real.sqrt_sq (norm_nonneg _)]
  rw [hu2, hw2] at hcs
  calc Real.sqrt δ * ∑ ψ, ‖E ψ u‖ * ‖E ψ w‖ ≤ Real.sqrt δ * (‖u‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
    _ = Real.sqrt δ * ‖u‖ * ‖w‖ := by ring

end Heis2

end KasH



open Matrix

namespace KasI

abbrev Ms (s : ℕ) := Matrix (Fin s) (Fin s) (ZMod 2)

/-- the right ideal annihilated by a character -/
def Kψ {s : ℕ} (ψ : AddChar (Ms s) ℂ) : AddSubgroup (Ms s) where
  carrier := {a | ∀ r, ψ (a * r) = 1}
  add_mem' {a b} ha hb r := by rw [add_mul, AddChar.map_add_eq_mul, ha r, hb r, one_mul]
  zero_mem' r := by rw [zero_mul, AddChar.map_zero_eq_one]
  neg_mem' {a} ha r := by
    rw [neg_mul, AddChar.map_neg_eq_inv, ha r, inv_one]

theorem mul_mem_K {s : ℕ} (ψ : AddChar (Ms s) ℂ) {a : Ms s} (ha : a ∈ Kψ ψ) (t : Ms s) :
    a * t ∈ Kψ ψ := fun r => by rw [mul_assoc]; exact ha (t * r)

theorem index_bound {s : ℕ} (ψ : AddChar (Ms s) ℂ) (hψ : ψ ≠ 1) :
    2 ^ s * Nat.card (Kψ ψ) ≤ Nat.card (Ms s) := by
  -- some diagonal unit is outside `K`
  have h1 : (1 : Ms s) ∉ Kψ ψ := by
    intro h
    apply hψ
    ext r
    have := h r
    rw [one_mul] at this
    rw [this]; rfl
  obtain ⟨i, hi⟩ : ∃ i, single i i (1 : ZMod 2) ∉ Kψ ψ := by
    by_contra hc
    push Not at hc
    apply h1
    rw [← sum_single_one]
    exact AddSubgroup.sum_mem _ fun i _ => hc i
  -- injective map into the quotient
  let φ : (Fin s → ZMod 2) → Ms s ⧸ Kψ ψ :=
    fun c => QuotientAddGroup.mk (∑ j, single i j (c j))
  have hφ : Function.Injective φ := by
    intro c c' h
    rw [QuotientAddGroup.eq] at h
    by_contra hne
    obtain ⟨j0, hj0⟩ : ∃ j, c j ≠ c' j := by
      by_contra hc; push Not at hc; exact hne (funext hc)
    have hmem := mul_mem_K ψ h (single j0 i 1)
    have hcalc : (-(∑ j, single i j (c j)) + ∑ j, single i j (c' j)) * single j0 i (1 : ZMod 2) =
        single i i (c' j0 - c j0) := by
      ext a b
      simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.sum_apply,
        Matrix.single_apply, mul_ite, mul_one, mul_zero]
      by_cases ha : i = a <;> by_cases hb : i = b
      · subst ha; subst hb
        simp [Finset.sum_ite_eq', Finset.sum_ite_eq]
        generalize c j0 = x; generalize c' j0 = y
        revert x y; decide
      · simp [hb]
      · simp [ha]
      · simp [ha]
    rw [hcalc] at hmem
    have h1' : c' j0 - c j0 = 1 := by
      have : ∀ x y : ZMod 2, x ≠ y → y - x = 1 := by decide
      exact this _ _ hj0
    rw [h1'] at hmem
    exact hi hmem
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (Kψ ψ)
  have hq : 2 ^ s ≤ Nat.card (Ms s ⧸ Kψ ψ) := by
    have := Nat.card_le_card_of_injective φ hφ
    simpa [Nat.card_eq_fintype_card, ZMod.card] using this
  rw [hcard]
  exact Nat.mul_le_mul_right _ hq

end KasI



open DepthOneQExp Matrix

namespace KasBlk2

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

theorem add_self_M (M : Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2)) : M + M = 0 := by
  ext p q; simp only [Matrix.add_apply, Matrix.zero_apply]
  generalize M p q = c; revert c; decide

theorem gen_two_zsmul {M : Type} [AddGroup M] (a : M) : (2 : ℤ) • a = a + a := two_zsmul a

theorem gen_three_zsmul {M : Type} [AddGroup M] (a : M) : (3 : ℤ) • a = a + a + a := by
  rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, two_zsmul, one_zsmul]

theorem gen_four_zsmul {M : Type} [AddGroup M] (a : M) : (4 : ℤ) • a = a + a + (a + a) := by
  rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul, two_zsmul]

theorem neg_M (M : Matrix (Fin 3 × Fin s) (Fin 3 × Fin s) (ZMod 2)) : -M = M := by
  ext p q; simp only [Matrix.neg_apply]; exact ZMod.neg_eq_self_mod_two _




theorem comm_02 (a : Ms s) :
    E 0 1 (by decide) a * E 1 2 (by decide) 1 * E 0 1 (by decide) a * E 1 2 (by decide) 1 =
      E 0 2 (by decide) a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem comm_10 (a : Ms s) :
    E 1 2 (by decide) a * E 2 0 (by decide) 1 * E 1 2 (by decide) a * E 2 0 (by decide) 1 =
      E 1 0 (by decide) a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem comm_21 (a : Ms s) :
    E 2 0 (by decide) a * E 0 1 (by decide) 1 * E 2 0 (by decide) a * E 0 1 (by decide) 1 =
      E 2 1 (by decide) a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem ι_Nb_single (a b : Fin 3) (i j : Fin s) :
    ι s (1 + Nb s a b (single i j 1)) =
      transvection (finProdFinEquiv (a, i)) (finProdFinEquiv (b, j)) 1 := by
  rw [transvection]
  simp only [map_add, map_one]
  congr 1
  rw [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  ext p q
  simp only [Matrix.submatrix_apply, Nb, of_apply, Matrix.single_apply]
  obtain ⟨⟨c, k⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨d, l⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h1 : c = a <;> by_cases h2 : d = b <;> by_cases h3 : i = k <;> by_cases h4 : j = l <;>
    simp_all [eq_comm]

/-- a cross-block transvection is a block elementary matrix -/
theorem transvection_cross (a b : Fin 3) (hab : a ≠ b) (i j : Fin s) :
    ((E a b hab (single i j 1) : SLs s) : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) =
      transvection (finProdFinEquiv (a, i)) (finProdFinEquiv (b, j)) 1 := by
  rw [coe_E, ι_Nb_single]

/-- an in-block transvection is a product of four block elementary matrices -/
theorem transvection_in (a c : Fin 3) (hac : a ≠ c) (i j : Fin s) (hij : i ≠ j) :
    ((E a c hac (single i j 1) * E c a hac.symm (single j j 1) * E a c hac (single i j 1) *
      E c a hac.symm (single j j 1) : SLs s) : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2)) =
      transvection (finProdFinEquiv (a, i)) (finProdFinEquiv (a, j)) 1 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  rw [← ι_Nb_single]
  congr 1
  set P := Nb s a c (single i j 1)
  set Q := Nb s c a (single j j 1)
  have hPP : P * P = 0 := by rw [Nb_mul_Nb, if_neg hac.symm]
  have hQQ : Q * Q = 0 := by rw [Nb_mul_Nb, if_neg hac]
  have hPQ : P * Q = Nb s a a (single i j 1) := by
    rw [Nb_mul_Nb, if_pos rfl, single_mul_single_same, mul_one]
  have hQP : Q * P = 0 := by
    rw [Nb_mul_Nb, if_pos rfl, single_mul_single_of_ne _ _ _ _ (Ne.symm hij), Nb_zero]
  have hPP' := add_self_M P
  have hQQ' := add_self_M Q
  rw [← hPQ]
  clear_value P Q
  have s1 : (1 + P) * (1 + Q) = 1 + P + Q + P * Q := by noncomm_ring
  have s2 : (1 + P + Q + P * Q) * (1 + P) = 1 + Q + P * Q := by
    have : (1 + P + Q + P * Q) * (1 + P) = 1 + (P + P) + Q + P * Q + P * P + Q * P + P * (Q * P) := by
      noncomm_ring
    rw [this, hPP', hPP, hQP, mul_zero]; abel
  have s3 : (1 + Q + P * Q) * (1 + Q) = 1 + P * Q := by
    have : (1 + Q + P * Q) * (1 + Q) = 1 + (Q + Q) + P * Q + Q * Q + P * (Q * Q) := by noncomm_ring
    rw [this, hQQ', hQQ, mul_zero]; abel
  rw [s1, s2, s3]

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

/-- a transvection structure as an element of `SL` -/
def tsl (t : TransvectionStruct (Fin (3 * s)) (ZMod 2)) : SLs s :=
  ⟨t.toMatrix, det_transvection_of_ne t.i t.j t.hij t.c⟩

theorem coe_list_prod_tsl (L : List (TransvectionStruct (Fin (3 * s)) (ZMod 2))) :
    ((L.map tsl).prod : SLs s).1 = (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => rfl
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    show (tsl t).1 * ((L.map tsl).prod).1 = _
    rw [ih]; rfl

/-- `X₁₂`, `X₂₃`, `X₃₁` generate `SL(3s; 𝔽₂)` -/
theorem gen_top (S : Subgroup (SLs s))
    (h01 : ∀ r, E 0 1 (by decide) r ∈ S) (h12 : ∀ r, E 1 2 (by decide) r ∈ S)
    (h20 : ∀ r, E 2 0 (by decide) r ∈ S) : ∀ g, g ∈ S := by
  have h02 : ∀ r, E 0 2 (by decide) r ∈ S := fun r => by
    rw [← comm_02]; exact S.mul_mem (S.mul_mem (S.mul_mem (h01 r) (h12 1)) (h01 r)) (h12 1)
  have h10 : ∀ r, E 1 0 (by decide) r ∈ S := fun r => by
    rw [← comm_10]; exact S.mul_mem (S.mul_mem (S.mul_mem (h12 r) (h20 1)) (h12 r)) (h20 1)
  have h21 : ∀ r, E 2 1 (by decide) r ∈ S := fun r => by
    rw [← comm_21]; exact S.mul_mem (S.mul_mem (S.mul_mem (h20 r) (h01 1)) (h20 r)) (h01 1)
  have hE : ∀ (a b : Fin 3) (hab : a ≠ b) r, E a b hab r ∈ S := by
    intro a b hab r
    fin_cases a <;> fin_cases b
    all_goals first
      | exact absurd rfl hab
      | exact h01 r | exact h02 r | exact h10 r | exact h12 r | exact h20 r | exact h21 r
  have ht : ∀ t : TransvectionStruct (Fin (3 * s)) (ZMod 2), tsl t ∈ S := by
    intro t
    rcases zmod2_cases t.c with hc | hc
    · have : tsl t = 1 := by
        apply Subtype.ext
        show t.toMatrix = 1
        rw [TransvectionStruct.toMatrix, hc, transvection_zero]
      rw [this]; exact S.one_mem
    · obtain ⟨⟨a, i⟩, hp⟩ := finProdFinEquiv.surjective t.i
      obtain ⟨⟨b, j⟩, hq⟩ := finProdFinEquiv.surjective t.j
      by_cases hab : a = b
      · subst hab
        have hij : i ≠ j := by
          intro h; subst h; exact t.hij (hp.symm.trans hq)
        set c : Fin 3 := a + 1
        have hac : a ≠ c := by fin_cases a <;> decide
        have : tsl t = E a c hac (single i j 1) * E c a hac.symm (single j j 1) *
            E a c hac (single i j 1) * E c a hac.symm (single j j 1) := by
          apply Subtype.ext
          rw [transvection_in a c hac i j hij]
          show t.toMatrix = _
          rw [TransvectionStruct.toMatrix, hc, ← hp, ← hq]
        rw [this]
        exact S.mul_mem (S.mul_mem (S.mul_mem (hE _ _ _ _) (hE _ _ _ _)) (hE _ _ _ _)) (hE _ _ _ _)
      · have : tsl t = E a b hab (single i j 1) := by
          apply Subtype.ext
          rw [transvection_cross a b hab i j]
          show t.toMatrix = _
          rw [TransvectionStruct.toMatrix, hc, ← hp, ← hq]
        rw [this]; exact hE _ _ _ _
  have hlist : ∀ L : List (TransvectionStruct (Fin (3 * s)) (ZMod 2)), (L.map tsl).prod ∈ S := by
    intro L
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
    exact ht t
  intro g
  obtain ⟨L, L', D, hg⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec
    (g : Matrix (Fin (3 * s)) (Fin (3 * s)) (ZMod 2))
  have h1 : ∀ L : List (TransvectionStruct (Fin (3 * s)) (ZMod 2)),
      (L.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro L
    rw [← coe_list_prod_tsl]
    exact ((L.map tsl).prod).prop
  have hdet : (diagonal D).det = 1 := by
    have := congrArg Matrix.det hg
    rw [g.prop, det_mul, det_mul, h1, h1, one_mul, mul_one] at this
    exact this.symm
  have hD : diagonal D = 1 := by
    rw [det_diagonal] at hdet
    have : ∀ i, D i = 1 := by
      intro i
      rcases zmod2_cases (D i) with h0 | h1'
      · exfalso
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0] at hdet
        exact zero_ne_one hdet
      · exact h1'
    ext a b
    simp [diagonal, Matrix.one_apply, this]
  have hg' : g = (L.map tsl).prod * (L'.map tsl).prod := by
    apply Subtype.ext
    show g.1 = ((L.map tsl).prod).1 * ((L'.map tsl).prod).1
    rw [coe_list_prod_tsl, coe_list_prod_tsl, show g.1 = _ from hg, hD, mul_one]
  rw [hg']
  exact S.mul_mem (hlist L) (hlist L')

end KasBlk2



open scoped InnerProductSpace
open KasF KasG KasH KasI KasBlk2 DepthOneQExp Matrix

namespace KasK2

variable {s : ℕ} (ρ : ConstGapCircuits.UnitaryRep (SLs s))

noncomputable def U (g : SLs s) : EuclideanSpace ℂ (Fin ρ.dim) →L[ℂ] EuclideanSpace ℂ (Fin ρ.dim) :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ)

theorem U_mul (g h : SLs s) : U ρ (g * h) = U ρ g * U ρ h := by
  simp only [U, map_mul]
  rw [Submonoid.coe_mul, map_mul]

theorem U_one : U ρ 1 = 1 := by simp [U]

theorem U_adj (g : SLs s) : ContinuousLinearMap.adjoint (U ρ g) = U ρ g⁻¹ := by
  rw [U, ← ContinuousLinearMap.star_eq_adjoint, ← map_star, U, map_inv]
  rfl

/-- a root subgroup as a unitary representation of `(Mat_s, +)` -/
noncomputable def rootHom (a b : Fin 3) (hab : a ≠ b)
    (hadd : ∀ r t : KasBlk2.Ms s, E a b hab (r + t) = E a b hab r * E a b hab t) : Hom (KasBlk2.Ms s)
      (EuclideanSpace ℂ (Fin ρ.dim)) where
  T r := U ρ (E a b hab r)
  map_zero := by rw [E_zero, U_one]
  map_add r t := by rw [hadd, U_mul]
  adj r := by
    rw [U_adj]
    congr 1
    have : E a b hab (-r) * E a b hab r = 1 := by rw [← hadd, neg_add_cancel, E_zero]
    exact (eq_inv_of_mul_eq_one_left this).symm

theorem add01 (r t : KasBlk2.Ms s) :
    E 0 1 (by decide) (r + t) = (E 0 1 (by decide) r * E 0 1 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem add12 (r t : KasBlk2.Ms s) :
    E 1 2 (by decide) (r + t) = (E 1 2 (by decide) r * E 1 2 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem add20 (r t : KasBlk2.Ms s) :
    E 2 0 (by decide) (r + t) = (E 2 0 (by decide) r * E 2 0 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem add02 (r t : KasBlk2.Ms s) :
    E 0 2 (by decide) (r + t) = (E 0 2 (by decide) r * E 0 2 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem add10 (r t : KasBlk2.Ms s) :
    E 1 0 (by decide) (r + t) = (E 1 0 (by decide) r * E 1 0 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem add21 (r t : KasBlk2.Ms s) :
    E 2 1 (by decide) (r + t) = (E 2 1 (by decide) r * E 2 1 (by decide) t : SLs s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem relA (a b : KasBlk2.Ms s) : (E 0 1 (by decide) a * E 1 2 (by decide) b : SLs s) =
    E 1 2 (by decide) b * E 0 1 (by decide) a * E 0 2 (by decide) (a * b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem relB (a b : KasBlk2.Ms s) : (E 2 0 (by decide) a * E 0 1 (by decide) b : SLs s) =
    E 0 1 (by decide) b * E 2 0 (by decide) a * E 2 1 (by decide) (a * b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem relC (a b : KasBlk2.Ms s) : (E 1 2 (by decide) a * E 2 0 (by decide) b : SLs s) =
    E 2 0 (by decide) b * E 1 2 (by decide) a * E 1 0 (by decide) (a * b) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz02_01 (c a : KasBlk2.Ms s) : (E 0 2 (by decide) c * E 0 1 (by decide) a : SLs s) =
    E 0 1 (by decide) a * E 0 2 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz02_12 (c a : KasBlk2.Ms s) : (E 0 2 (by decide) c * E 1 2 (by decide) a : SLs s) =
    E 1 2 (by decide) a * E 0 2 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz21_20 (c a : KasBlk2.Ms s) : (E 2 1 (by decide) c * E 2 0 (by decide) a : SLs s) =
    E 2 0 (by decide) a * E 2 1 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz21_01 (c a : KasBlk2.Ms s) : (E 2 1 (by decide) c * E 0 1 (by decide) a : SLs s) =
    E 0 1 (by decide) a * E 2 1 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz10_12 (c a : KasBlk2.Ms s) : (E 1 0 (by decide) c * E 1 2 (by decide) a : SLs s) =
    E 1 2 (by decide) a * E 1 0 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem cz10_20 (c a : KasBlk2.Ms s) : (E 1 0 (by decide) c * E 2 0 (by decide) a : SLs s) =
    E 2 0 (by decide) a * E 1 0 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_E, ← map_mul]
  congr 1
  simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, Nb_mul_Nb, mul_assoc, Nb_add, Nb_sub,
    Fin.reduceEq, if_true, if_false, zero_mul, mul_zero, add_zero, zero_add, Fin.isValue]
  try abel_nf
  try simp only [gen_two_zsmul, gen_three_zsmul, gen_four_zsmul, neg_one_zsmul, neg_M, add_self_M,
    add_zero, zero_add, one_zsmul]
  try abel

theorem hidx_ms (hs : 1 ≤ s) (ψ : AddChar (KasBlk2.Ms s) ℂ) (hψ : ψ ≠ 1) :
    ((Finset.univ.filter fun a : KasBlk2.Ms s => ∀ r, ψ (a * r) = 1).card : ℝ) ≤
      (1 / 2) ^ s * Fintype.card (KasBlk2.Ms s) := by
  have h := index_bound (s := s) ψ hψ
  have e1 : Nat.card (Kψ ψ) = (Finset.univ.filter fun a : KasBlk2.Ms s => ∀ r, ψ (a * r) = 1).card := by
    have hset : ((Kψ ψ : AddSubgroup (KasBlk2.Ms s)) : Set (KasBlk2.Ms s)) =
        ↑(Finset.univ.filter fun a : KasBlk2.Ms s => ∀ r, ψ (a * r) = 1) := by
      ext a; simp [Kψ]
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [e1, Nat.card_eq_fintype_card] at h
  have h2 : (2 : ℝ) ^ s * ((Finset.univ.filter fun a : KasBlk2.Ms s => ∀ r, ψ (a * r) = 1).card : ℝ) ≤
      Fintype.card (KasBlk2.Ms s) := by exact_mod_cast h
  have h3 : (0 : ℝ) < 2 ^ s := by positivity
  rw [one_div, inv_pow, inv_mul_eq_div, le_div_iff₀ h3]
  linarith

/-- averaging: some element of a root subgroup moves `v` at least as much as `v` is far from the
fixed space -/
theorem tenth_of_sq {w : EuclideanSpace ℂ (Fin ρ.dim)} (h : 1 / 20 ≤ ‖w‖ ^ 2) : 1 / 10 ≤ ‖w‖ := by
  nlinarith [norm_nonneg w]

theorem exists_far (X : Hom (KasBlk2.Ms s) (EuclideanSpace ℂ (Fin ρ.dim)))
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (c : ℝ)
    (h : c ≤ ‖v - (fixSub X.T).starProjection v‖) : ∃ r, c ≤ ‖X.T r v - v‖ := by
  have h1 : ‖v - (fixSub X.T).starProjection v‖ ≤ ‖v - avg X v‖ :=
    dist_proj_le _ v _ (avg_mem X v)
  have h2 : v - avg X v = (1 / (Fintype.card (KasBlk2.Ms s) : ℂ)) • ∑ r, (v - X.T r v) := by
    rw [avg_eq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
      inv_mul_cancel₀ card_ne, one_smul]
  by_contra hc
  push Not at hc
  have hcard : (0 : ℝ) < Fintype.card (KasBlk2.Ms s) := by exact_mod_cast Fintype.card_pos
  have h3 : ‖v - avg X v‖ < c := by
    rw [h2, norm_smul, norm_div, norm_one, Complex.norm_natCast]
    have : ‖∑ r, (v - X.T r v)‖ < Fintype.card (KasBlk2.Ms s) * c := by
      calc ‖∑ r, (v - X.T r v)‖ ≤ ∑ r : KasBlk2.Ms s, ‖v - X.T r v‖ := norm_sum_le _ _
        _ < ∑ _r : KasBlk2.Ms s, c := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
            (fun r _ => by rw [norm_sub_rev]; exact hc r)
        _ = Fintype.card (KasBlk2.Ms s) * c := by simp
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hcard]
    linarith
  linarith

end KasK2

open KasK2 in
theorem solution (s : ℕ) (hs : 3 ≤ s)
    (ρ : ConstGapCircuits.UnitaryRep (Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2)))
    (hρ : ∀ v : EuclideanSpace ℂ (Fin ρ.dim),
      (∀ g, Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom g : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v = v) → v = 0)
    (v : EuclideanSpace ℂ (Fin ρ.dim)) (hv : ‖v‖ = 1) :
    ∃ r : Matrix (Fin s) (Fin s) (ZMod 2),
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 0 1 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ∨
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 1 2 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ ∨
      (1 / 10 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (ρ.hom (show Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) from ⟨blockElem s 2 0 r, det_blockElem s (by decide) r⟩) : Matrix (Fin ρ.dim) (Fin ρ.dim) ℂ) v - v‖ := by
  set X1 := rootHom ρ 0 1 (by decide) add01
  set X2 := rootHom ρ 1 2 (by decide) add12
  set X3 := rootHom ρ 2 0 (by decide) add20
  set Z02 := rootHom ρ 0 2 (by decide) add02
  set Z10 := rootHom ρ 1 0 (by decide) add10
  set Z21 := rootHom ρ 2 1 (by decide) add21
  have hs1 : 1 ≤ s := by omega
  have hidx := hidx_ms hs1
  have hδ : (0 : ℝ) ≤ (1 / 2) ^ s := by positivity
  -- the three pairs
  have o12 := heis_orth X1 X2 Z02
    (fun a b => by simp only [X1, X2, Z02, rootHom]; rw [← U_mul, ← U_mul, ← U_mul, relA])
    (fun c a => by simp only [X1, Z02, rootHom]; rw [← U_mul, ← U_mul, cz02_01])
    (fun c b => by simp only [X2, Z02, rootHom]; rw [← U_mul, ← U_mul, cz02_12]) _ hδ hidx
  have o31 := heis_orth X3 X1 Z21
    (fun a b => by simp only [X1, X3, Z21, rootHom]; rw [← U_mul, ← U_mul, ← U_mul, relB])
    (fun c a => by simp only [X3, Z21, rootHom]; rw [← U_mul, ← U_mul, cz21_20])
    (fun c b => by simp only [X1, Z21, rootHom]; rw [← U_mul, ← U_mul, cz21_01]) _ hδ hidx
  have o23 := heis_orth X2 X3 Z10
    (fun a b => by simp only [X2, X3, Z10, rootHom]; rw [← U_mul, ← U_mul, ← U_mul, relC])
    (fun c a => by simp only [X2, Z10, rootHom]; rw [← U_mul, ← U_mul, cz10_12])
    (fun c b => by simp only [X3, Z10, rootHom]; rw [← U_mul, ← U_mul, cz10_20]) _ hδ hidx
  have o13 : Orth (fixSub X1.T ⊓ (fixSub X1.T ⊓ fixSub X3.T)ᗮ) (fixSub X3.T ⊓ (fixSub X1.T ⊓ fixSub X3.T)ᗮ)
      (Real.sqrt ((1 / 2) ^ s)) := by
    have := orth_symm o31
    rwa [inf_comm (fixSub X3.T) (fixSub X1.T)] at this
  have hε2 : Real.sqrt ((1 / 2) ^ s) ^ 2 ≤ 1 / 8 := by
    rw [Real.sq_sqrt hδ]
    calc ((1 : ℝ) / 2) ^ s ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
      _ = 1 / 8 := by norm_num
  -- triple intersection
  have htriple : ∀ x, x ∈ fixSub X1.T → x ∈ fixSub X2.T → x ∈ fixSub X3.T → x = 0 := by
    intro x h1 h2 h3
    let S : Subgroup (SLs s) :=
      { carrier := {g | U ρ g x = x}
        one_mem' := by show U ρ 1 x = x; rw [U_one]; rfl
        mul_mem' := fun {g h} hg hh => by
          show U ρ (g * h) x = x
          rw [U_mul, ContinuousLinearMap.mul_apply, show U ρ h x = x from hh, show U ρ g x = x from hg]
        inv_mem' := fun {g} hg => by
          show U ρ g⁻¹ x = x
          have : U ρ g⁻¹ (U ρ g x) = x := by
            rw [← ContinuousLinearMap.mul_apply, ← U_mul, inv_mul_cancel, U_one]; rfl
          rwa [show U ρ g x = x from hg] at this }
    have hall := gen_top S (fun r => h1 r) (fun r => h2 r) (fun r => h3 r)
    exact hρ x fun g => hall g
  rcases three_far (Real.sqrt_nonneg _) hε2 o12 o13 o23 htriple v with h | h | h
  · rw [hv, one_pow, mul_one] at h
    obtain ⟨r, hr⟩ := exists_far ρ X1 v _ (tenth_of_sq ρ h)
    exact ⟨r, Or.inl hr⟩
  · rw [hv, one_pow, mul_one] at h
    obtain ⟨r, hr⟩ := exists_far ρ X2 v _ (tenth_of_sq ρ h)
    exact ⟨r, Or.inr (Or.inl hr)⟩
  · rw [hv, one_pow, mul_one] at h
    obtain ⟨r, hr⟩ := exists_far ρ X3 v _ (tenth_of_sq ρ h)
    exact ⟨r, Or.inr (Or.inr hr)⟩
