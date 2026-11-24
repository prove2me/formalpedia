-- Prove2me | solution 1 for DepthOneQExp.eq_2_43
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:57:46.456566+00:00
-- url     : https://prove2.me/submissions/a8c85045-3b4c-4452-8147-29c7c38f43bc

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_cnotAvg
import Definitions.Def_DepthOneQExp_spanProj
import Definitions.Def_DepthOneQExp_gamma
import Theorems.Thm_DepthOneQExp_gamma_cnot_and_range

open DepthOneQExp Matrix
open scoped Kronecker

namespace DepthOneQExp.Eq243Aux

variable {n : ℕ}

abbrev V (n : ℕ) := Fin n → ZMod 2

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem equiv_two {α β : Type*} [DecidableEq β] (g : α ≃ β) (a1 a2 : α) (b1 b2 : β)
    (ha : a1 ≠ a2) (hb : b1 ≠ b2) : ∃ f : α ≃ β, f a1 = b1 ∧ f a2 = b2 := by
  let f1 := g.trans (Equiv.swap (g a1) b1)
  have h1 : f1 a1 = b1 := by simp [f1]
  have h12 : f1 a2 ≠ b1 := by rw [← h1]; exact fun h => ha (f1.injective h).symm
  refine ⟨f1.trans (Equiv.swap (f1 a2) b2), ?_, ?_⟩
  · simp only [Equiv.trans_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne h12.symm hb
  · simp

theorem lin_pair (x y : V n) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndepOn (ZMod 2) id ({x, y} : Set (V n)) := by
  apply linearIndepOn_id_pair hx
  intro a
  rcases zmod2_cases a with rfl | rfl
  · simpa using hy.symm
  · simpa using hxy

theorem exists_lequiv (x y x' y' : V n) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) (hxy' : x' ≠ y') :
    ∃ L : V n ≃ₗ[ZMod 2] V n, L x = x' ∧ L y = y' := by
  classical
  have hs := lin_pair x y hx hy hxy
  have hs' := lin_pair x' y' hx' hy' hxy'
  let b := Module.Basis.extend hs
  let b' := Module.Basis.extend hs'
  have mx : x ∈ hs.extend (Set.subset_univ _) := hs.subset_extend _ (by simp)
  have my : y ∈ hs.extend (Set.subset_univ _) := hs.subset_extend _ (by simp)
  have mx' : x' ∈ hs'.extend (Set.subset_univ _) := hs'.subset_extend _ (by simp)
  have my' : y' ∈ hs'.extend (Set.subset_univ _) := hs'.subset_extend _ (by simp)
  obtain ⟨f, hf1, hf2⟩ := equiv_two (b.indexEquiv b') ⟨x, mx⟩ ⟨y, my⟩ ⟨x', mx'⟩ ⟨y', my'⟩
    (fun h => hxy (congrArg Subtype.val h)) (fun h => hxy' (congrArg Subtype.val h))
  refine ⟨b.equiv b' f, ?_, ?_⟩
  · have := b.equiv_apply ⟨x, mx⟩ b' f
    rw [Module.Basis.extend_apply_self, hf1, Module.Basis.extend_apply_self] at this
    exact this
  · have := b.equiv_apply ⟨y, my⟩ b' f
    rw [Module.Basis.extend_apply_self, hf2, Module.Basis.extend_apply_self] at this
    exact this

theorem exists_SL (x y x' y' : V n) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) (hxy' : x' ≠ y') :
    ∃ g : SpecialLinearGroup (Fin n) (ZMod 2), (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x' ∧
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ y = y' := by
  obtain ⟨L, h1, h2⟩ := exists_lequiv x y x' y' hx hy hxy hx' hy' hxy'
  have hdet : (LinearMap.toMatrix' (L : V n →ₗ[ZMod 2] V n)).det = 1 := by
    rw [LinearMap.det_toMatrix']
    have := (LinearEquiv.isUnit_det' L).ne_zero
    rcases zmod2_cases (LinearMap.det (L : V n →ₗ[ZMod 2] V n)) with h | h
    · exact absurd h this
    · exact h
  refine ⟨⟨_, hdet⟩, ?_, ?_⟩
  · simp only [LinearMap.toMatrix'_mulVec]; exact h1
  · simp only [LinearMap.toMatrix'_mulVec]; exact h2

theorem gamma_apply (g : SpecialLinearGroup (Fin n) (ZMod 2)) (x : V n) :
    (gamma n g : MITMSynthesis.Q n → MITMSynthesis.Q n) x = (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := rfl

theorem mem_iff (σ : Equiv.Perm (MITMSynthesis.Q n)) :
    σ ∈ cnotGroup n ↔ ∃ g, gamma n g = σ := by
  rw [← (gamma_cnot_and_range n).2]; rfl

theorem gamma_mem (g : SpecialLinearGroup (Fin n) (ZMod 2)) : gamma n g ∈ cnotGroup n :=
  (mem_iff _).2 ⟨g, rfl⟩

theorem mem_fix_zero (σ : Equiv.Perm (MITMSynthesis.Q n)) (hσ : σ ∈ cnotGroup n) : σ 0 = 0 := by
  obtain ⟨g, rfl⟩ := (mem_iff σ).1 hσ
  exact (gamma_apply g 0).trans (mulVec_zero _)

/-- transitivity on pairs of distinct nonzero vectors -/
theorem trans_pair (x y x' y' : MITMSynthesis.Q n) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hx' : x' ≠ 0) (hy' : y' ≠ 0) (hxy' : x' ≠ y') :
    ∃ σ ∈ cnotGroup n, σ x = x' ∧ σ y = y' := by
  obtain ⟨g, h1, h2⟩ := exists_SL (n := n) x y x' y' hx hy hxy hx' hy' hxy'
  exact ⟨gamma n g, gamma_mem g, (gamma_apply g x).trans h1, (gamma_apply g y).trans h2⟩


theorem inv_mem_symm (σ : Equiv.Perm (MITMSynthesis.Q n)) (hσ : σ ∈ cnotGroup n) :
    σ.symm ∈ cnotGroup n := (cnotGroup n).inv_mem hσ

def e0 (n : ℕ) : MITMSynthesis.Q n := fun k => if (k : ℕ) = 0 then 1 else 0
def e1 (n : ℕ) : MITMSynthesis.Q n := fun k => if (k : ℕ) = 1 then 1 else 0

theorem e0_ne (hn : 2 ≤ n) : e0 n ≠ 0 := by
  intro h; have := congrFun h ⟨0, by omega⟩; simp [e0] at this
theorem e1_ne (hn : 2 ≤ n) : e1 n ≠ 0 := by
  intro h; have := congrFun h ⟨1, by omega⟩; simp [e1] at this
theorem e01_ne (hn : 2 ≤ n) : e0 n ≠ e1 n := by
  intro h; have := congrFun h ⟨0, by omega⟩; simp [e0, e1] at this

theorem trans_one (hn : 2 ≤ n) (x : MITMSynthesis.Q n) (hx : x ≠ 0) :
    ∃ σ ∈ cnotGroup n, σ (e0 n) = x := by
  by_cases h : x = e0 n
  · exact ⟨1, one_mem _, by simp [h]⟩
  · obtain ⟨σ, hσ, h1, _⟩ := trans_pair (e0 n) (e1 n) x (e0 n) (e0_ne hn) (e1_ne hn) (e01_ne hn)
      hx (e0_ne hn) h
    exact ⟨σ, hσ, h1⟩

/-- orbit constancy of invariant functions -/
theorem orbit_const (hn : 2 ≤ n) (w : MITMSynthesis.Q n × MITMSynthesis.Q n → ℂ)
    (hw : ∀ σ ∈ cnotGroup n, ∀ x y, w (σ x, σ y) = w (x, y)) (x y : MITMSynthesis.Q n) :
    w (x, y) = if x = 0 then (if y = 0 then w (0, 0) else w (0, e0 n)) else
      (if y = 0 then w (e0 n, 0) else if x = y then w (e0 n, e0 n) else w (e0 n, e1 n)) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst hx; subst hy; simp
  · subst hx; rw [if_pos rfl, if_neg hy]
    obtain ⟨σ, hσ, h1⟩ := trans_one hn y hy
    have := hw σ hσ 0 (e0 n); rw [mem_fix_zero σ hσ, h1] at this; exact this
  · subst hy; rw [if_neg hx, if_pos rfl]
    obtain ⟨σ, hσ, h1⟩ := trans_one hn x hx
    have := hw σ hσ (e0 n) 0; rw [mem_fix_zero σ hσ, h1] at this; exact this
  · rw [if_neg hx, if_neg hy]
    by_cases hxy : x = y
    · subst hxy; rw [if_pos rfl]
      obtain ⟨σ, hσ, h1⟩ := trans_one hn x hx
      rw [← h1, hw σ hσ]
    · rw [if_neg hxy]
      obtain ⟨σ, hσ, h1, h2⟩ := trans_pair (e0 n) (e1 n) x y (e0_ne hn) (e1_ne hn) (e01_ne hn)
        hx hy hxy
      rw [← h1, ← h2, hw σ hσ]


abbrev κ (n : ℕ) := MITMSynthesis.Q n × MITMSynthesis.Q n

theorem kron_perm {α : Type} [Fintype α] [DecidableEq α] (σ τ : Equiv.Perm α) :
    permToMatrix σ ⊗ₖ permToMatrix τ = permToMatrix (Equiv.prodCongr σ τ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [kroneckerMap_apply, permToMatrix, Equiv.prodCongr_apply, Prod.map, Prod.mk.injEq]
  by_cases h1 : a = σ c <;> by_cases h2 : b = τ d <;> simp [h1, h2]

theorem perm_mulVec {α : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (v : α → ℂ) :
    permToMatrix σ *ᵥ v = fun p => v (σ.symm p) := by
  funext p
  simp only [mulVec, dotProduct, permToMatrix, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm p)]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h; apply hb; rw [h, Equiv.symm_apply_apply]
  · simp

noncomputable def Wm (σ : Equiv.Perm (MITMSynthesis.Q n)) : Matrix (κ n) (κ n) ℂ :=
  permToMatrix (Equiv.prodCongr σ σ)

theorem Wm_mulVec (σ : Equiv.Perm (MITMSynthesis.Q n)) (v : κ n → ℂ) :
    Wm σ *ᵥ v = fun p => v (σ.symm p.1, σ.symm p.2) := by
  rw [Wm, perm_mulVec]; rfl

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

noncomputable def rr (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n))⁻¹ : ℝ)

theorem rr_ne : rr n ≠ 0 := by
  simp [rr]

theorem aVec_apply (i : Fin 5) (p : κ n) : aVec n i p =
    ![if p.1 = p.2 then 1 else 0, rr n * rr n,
      (if p.1 = 0 then 1 else 0) * (if p.2 = 0 then 1 else 0),
      (if p.1 = 0 then 1 else 0) * rr n, rr n * (if p.2 = 0 then 1 else 0)] i := by
  fin_cases i <;> rfl

theorem Wm_aVec (σ : Equiv.Perm (MITMSynthesis.Q n)) (hσ : σ ∈ cnotGroup n) (i : Fin 5) :
    Wm σ *ᵥ aVec n i = aVec n i := by
  rw [Wm_mulVec]
  funext ⟨x, y⟩
  have h0 := mem_fix_zero _ (inv_mem_symm σ hσ)
  have hz : ∀ z, σ.symm z = 0 ↔ z = 0 := fun z => by
    constructor
    · intro h; exact σ.symm.injective (h.trans h0.symm)
    · rintro rfl; exact h0
  have hi : σ.symm x = σ.symm y ↔ x = y := σ.symm.injective.eq_iff
  simp only [aVec_apply, hz, hi]

theorem cnotAvg_aVec (i : Fin 5) : cnotAvg n *ᵥ aVec n i = aVec n i := by
  rw [cnotAvg_eq, smul_mulVec, sum_mulVec]
  simp_rw [fun g : cnotGroup n => Wm_aVec (g : Equiv.Perm (MITMSynthesis.Q n)) g.2 i]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, one_div,
    inv_mul_cancel₀ card_ne, one_smul]

theorem cnotAvg_inv (v : κ n → ℂ) (σ : Equiv.Perm (MITMSynthesis.Q n)) (hσ : σ ∈ cnotGroup n)
    (x y : MITMSynthesis.Q n) : (cnotAvg n *ᵥ v) (σ x, σ y) = (cnotAvg n *ᵥ v) (x, y) := by
  have h := Wm_mul_cnotAvg (n := n) ⟨σ⁻¹, (cnotGroup n).inv_mem hσ⟩
  have h2 := congrArg (fun A => A *ᵥ v) h
  simp only [← mulVec_mulVec] at h2
  rw [Wm_mulVec] at h2
  have := congrFun h2 (x, y)
  simpa [Equiv.Perm.inv_def] using this

abbrev K (n : ℕ) : Submodule ℂ (EuclideanSpace ℂ (κ n)) :=
  Submodule.span ℂ (Set.range fun i : Fin 5 => WithLp.toLp 2 (aVec n i))

theorem mem_K_of_eq (w : κ n → ℂ) (c : Fin 5 → ℂ) (h : ∀ p, w p = ∑ i, c i * aVec n i p) :
    WithLp.toLp 2 w ∈ K n := by
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, ?_⟩
  simp only [← WithLp.toLp_smul, ← WithLp.toLp_sum]
  congr 1
  funext p
  simp [Finset.sum_apply, h p]


theorem mem_K_of_inv (hn : 2 ≤ n) (w : κ n → ℂ)
    (hw : ∀ σ ∈ cnotGroup n, ∀ x y, w (σ x, σ y) = w (x, y)) : WithLp.toLp 2 w ∈ K n := by
  have hr := rr_ne (n := n)
  apply mem_K_of_eq w ![w (e0 n, e0 n) - w (e0 n, e1 n), w (e0 n, e1 n) / rr n ^ 2,
    w (0, 0) - w (e0 n, e0 n) - w (0, e0 n) - w (e0 n, 0) + 2 * w (e0 n, e1 n),
    (w (0, e0 n) - w (e0 n, e1 n)) / rr n, (w (e0 n, 0) - w (e0 n, e1 n)) / rr n]
  rintro ⟨x, y⟩
  rw [orbit_const hn w hw x y]
  simp only [Fin.sum_univ_five, aVec_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst hx; subst hy; simp; field_simp; ring
  · subst hx
    have : (0 : MITMSynthesis.Q n) ≠ y := fun h => hy h.symm
    simp [hy, this]; field_simp; ring
  · subst hy; simp [hx]; field_simp; ring
  · by_cases hxy : x = y
    · subst hxy; simp [hx]; field_simp; ring
    · simp [hx, hy, hxy]; field_simp


theorem toE_spanProj :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (spanProj n) = (K n).starProjection := by
  simp [spanProj]

theorem spanProj_mulVec (u : κ n → ℂ) :
    WithLp.toLp 2 (spanProj n *ᵥ u) = (K n).starProjection (WithLp.toLp 2 u) := by
  rw [← toE_spanProj]; rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem spanProj_herm : (spanProj n)ᴴ = spanProj n := by
  rw [← Matrix.star_eq_conjTranspose]
  show star ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n)).symm (K n).starProjection) =
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n)).symm (K n).starProjection
  rw [← map_star, (isSelfAdjoint_starProjection (K n)).star_eq]

theorem cnotAvg_fix (u : EuclideanSpace ℂ (κ n)) (hu : u ∈ K n) :
    cnotAvg n *ᵥ WithLp.ofLp u = WithLp.ofLp u := by
  have hle : K n ≤ LinearMap.ker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ n) (cnotAvg n) :
      EuclideanSpace ℂ (κ n) →ₗ[ℂ] EuclideanSpace ℂ (κ n)) - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      ContinuousLinearMap.coe_coe, toEuclideanCLM_toLp, cnotAvg_aVec, sub_self]
  have := hle hu
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, sub_eq_zero] at this
  have h2 := congrArg WithLp.ofLp this
  rwa [ofLp_toEuclideanCLM] at h2

theorem spanProj_mul_cnotAvg (hn : 2 ≤ n) : spanProj n * cnotAvg n = cnotAvg n := by
  apply Matrix.mulVec_injective
  funext v
  rw [← mulVec_mulVec]
  have hmem : WithLp.toLp 2 (cnotAvg n *ᵥ v) ∈ K n :=
    mem_K_of_inv hn _ fun σ hσ x y => cnotAvg_inv v σ hσ x y
  apply WithLp.toLp_injective 2
  rw [spanProj_mulVec, Submodule.starProjection_eq_self_iff.2 hmem]

theorem cnotAvg_mul_spanProj : cnotAvg n * spanProj n = spanProj n := by
  apply Matrix.mulVec_injective
  funext v
  rw [← mulVec_mulVec]
  have hmem : WithLp.toLp 2 (spanProj n *ᵥ v) ∈ K n := by
    rw [spanProj_mulVec]; exact Submodule.starProjection_apply_mem _ _
  exact cnotAvg_fix _ hmem

end DepthOneQExp.Eq243Aux

open DepthOneQExp.Eq243Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) : cnotAvg n = spanProj n := by
  have h1 := spanProj_mul_cnotAvg hn
  have h2 := cnotAvg_mul_spanProj (n := n)
  calc cnotAvg n = (cnotAvg n)ᴴ := cnotAvg_herm.symm
    _ = (spanProj n * cnotAvg n)ᴴ := by rw [h1]
    _ = cnotAvg n * spanProj n := by rw [conjTranspose_mul, cnotAvg_herm, spanProj_herm]
    _ = spanProj n := h2
