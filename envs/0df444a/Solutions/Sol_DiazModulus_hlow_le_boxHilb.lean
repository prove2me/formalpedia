-- Prove2me | solution 1 for DiazModulus.hlow_le_boxHilb
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T09:57:59.883379+00:00
-- url     : https://prove2.me/submissions/9462cdb5-1e16-4a41-a9ff-335e77aa089b

import Mathlib
import Definitions.Def_DiazMultiplicity
import Theorems.Thm_DiazModulus_exists_tangent_dual
import Theorems.Thm_DiazModulus_exists_tangent_dual_cosets
import Theorems.Thm_DiazModulus_wustholz_le_boxHilb
import Theorems.Thm_DiazModulus_le_boxHilb_torusVanishing_subgroup
import Theorems.Thm_DiazModulus_exists_card_mul_boxHilb_le_translates
import Theorems.Thm_DiazModulus_boxHilb_anti
import Theorems.Thm_DiazModulus_box_ray_lower_bound
import Theorems.Thm_DiazModulus_restrictSupport_block_filtration
import Theorems.Thm_DiazModulus_torusTransl_algEquiv

open Complex ComplexConjugate

/-! # The lower bound for the Hilbert function of the obstruction ideal (DALAG §8.4.1)

DALAG (8.20) for the obstruction ideal `A`, vanishing to order `> M₀` along `W` on `Σ·Γ`. The tangent dual
(`exists_tangent_dual`, `n = dim W − dim (W ⊓ V × L)` derivations `w_i ∈ W` with dual functions `P_j` on `Γ`) is lifted to
the union of the cosets `Γ·g_s` (`exists_tangent_dual_cosets`), and Wüstholz's argument (`wustholz_le_boxHilb`) gives
`C(M₀ + n, n) · H(I(Σ·Γ); T) ≤ H(A; T + M₀·C_Q)`. For incongruent `s ≠ s′ ∈ Rₑ`, `g_s⁻¹ g_{s′} ∉ Γ`: it would lie in
`V × T_ψ`, i.e. `Σ_b (s′_b − s_b) u_b ∈ V` and `Π_i (Π_b a_{bi}^{s′_b − s_b})^{ψ_{ki}} = 1`, so `s′ = s` by
incongruence. Hence the translates `I(Γ·g_s) = σ_s I(Γ)` (`torusTransl_algEquiv`) are pairwise coprime
(`torusStab_subgroup`'s coprimality, carried by the hypothesis `hcop`), and
`exists_card_mul_boxHilb_le_translates` gives `|Rₑ| · H(I(Γ); T) ≤ H(⨅_s I(Γ·g_s); T + C₂)`; since every coset
`Γ·g_s` lies in `Σ·Γ`, `boxHilb_anti` passes to `I(Σ·Γ)`. Finally `H(I(Γ); tD) ≥ Π_{h∈H}(tD₀+1) Π_{j∈J}(2tD₁+1)`
(`le_boxHilb_torusVanishing_subgroup`) `≥ t^{|H|+|J|} D₀^{|H|} D₁^{|J|}` (`box_ray_lower_bound`), with
`|H| = dim V`, `|J| = dim L`. -/

namespace C13_Z6
open DiazModulus MvPolynomial

variable {A₀ A₁ : Type*}

/-- Membership in `I(S)`: vanishing at every point of `S`. -/
theorem mem_torusVanishing_iff {S : Set (TorusGroup ℂ A₀ A₁)} {f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ} :
    f ∈ torusVanishing S ↔ ∀ g ∈ S, eval (torusPt g) f = 0 := by
  simp [torusVanishing, Submodule.mem_iInf, RingHom.mem_ker]

end C13_Z6

open DiazModulus C13_Z6 MvPolynomial in
theorem solution {A₀ A₁ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁] (Γ : Subgroup (TorusGroup ℂ A₀ A₁))
    (hcop : ∀ g g' : TorusGroup ℂ A₀ A₁, g * g'⁻¹ ∉ Γ →
      torusVanishing {z | z * g ∈ Γ} ⊔ torusVanishing {z | z * g' ∈ Γ} = ⊤)
    (H : Finset A₀) (J : Finset A₁) (hH : ∀ x : A₀ → ℂ, ∃ v ∈ Submodule.span ℂ {v | ∃ g ∈ Γ, Multiplicative.toAdd g.1 = v}, ∀ h ∈ H, v h = x h)
    (hJ : ∀ φ : A₁ → ℤ, (∀ i ∉ J, φ i = 0) → (∀ g ∈ Γ, ∏ i, g.2 i ^ φ i = 1) → φ = 0)
    (ℓ : A₀ → A₀ → ℂ) (ψ : A₁ → A₁ → ℤ) (V : Submodule ℂ (A₀ → ℂ)) (L : Submodule ℂ (A₁ → ℂ))
    (hV : ∀ v, v ∈ V ↔ ∀ h, ∑ h', ℓ h h' * v h' = 0) (hL : ∀ v, v ∈ L ↔ ∀ i, ∑ i', (ψ i i' : ℂ) * v i' = 0)
    (hΓ : (Γ : Set (TorusGroup ℂ A₀ A₁)) ⊆ standardSet V ψ) (hVH : Module.finrank ℂ ↥V = H.card) (hLJ : Module.finrank ℂ ↥L = J.card)
    (W : Submodule ℂ ((A₀ → ℂ) × (A₁ → ℂ))) (n : ℕ) (hn : n + Module.finrank ℂ ↥(W ⊓ V.prod L) = Module.finrank ℂ ↥W)
    (u : B₁ → A₀ → ℂ) (a : B₁ → A₁ → ℂˣ) (M₀ M₁ : ℕ) (A : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ))
    (hA : (A : Set (MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ)) ⊆ vanishOrd (torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}) W M₀) (D₀ D₁ : ℕ) (Rₑ : Finset (B₁ → ℤ))
    (hR : ∀ s ∈ Rₑ, ∀ b, |s b| ≤ (M₁ : ℤ))
    (hRinc : ∀ s ∈ Rₑ, ∀ s' ∈ Rₑ, ((∑ b, ((s b - s' b : ℤ) : ℂ) • u b) ∈ V ∧
      ∀ k, ∏ i, (∏ b, a b i ^ (s b - s' b)) ^ ψ k i = 1) → s = s') :
    ∃ C : A₀ ⊕ A₁ → ℕ, ∀ t : ℕ, 1 ≤ t →
      (M₀ + n).choose n * Rₑ.card * D₀ ^ Module.finrank ℂ ↥V * D₁ ^ Module.finrank ℂ ↥L * t ^ ((Fintype.card A₀ + Fintype.card A₁) - ((Fintype.card A₀ + Fintype.card A₁) - (Module.finrank ℂ ↥V + Module.finrank ℂ ↥L)))
        ≤ boxHilb (torusBox ℂ A₀ A₁) A (t • boxD A₀ A₁ D₀ D₁ + C) := by
  classical
  obtain ⟨n', w, Pd, hn', hw, hP, hwP⟩ := exists_tangent_dual ℓ ψ V L hV hL W (Γ : Set (TorusGroup ℂ A₀ A₁)) hΓ
  have hnn : n' = n := by omega
  obtain ⟨Q, CQ, hQbox, hQJ, hwQ⟩ := exists_tangent_dual_cosets Γ hcop u a M₁ n' w Pd hP hwP
  -- the filtration facts for torusBox (C1.1's T1 at the block map of the model)
  obtain ⟨hFmul, hFfin, hFex⟩ :=
    restrictSupport_block_filtration (K := ℂ) (σ := A₀ ⊕ (A₁ × Bool)) (Sum.map id Prod.fst)
  have hmono : Monotone (torusBox ℂ A₀ A₁) := blockBox_mono ℂ _
  have hFfin' : ∀ T, FiniteDimensional ℂ ↥(torusBox ℂ A₀ A₁ T) := fun T => hFfin T
  -- the translations σ_s = τ_{g_s⁻¹} (V2), one for each s ∈ Rₑ
  choose e he using fun s : B₁ → ℤ => (torusTransl_algEquiv (hmePoint u a s)⁻¹).1
  have hinc : ∀ s ∈ Rₑ, ∀ s' ∈ Rₑ, s ≠ s' → (hmePoint u a s)⁻¹ * ((hmePoint u a s')⁻¹)⁻¹ ∉ Γ := by
    intro s hs s' hs' hne hmem
    obtain ⟨h1, h2⟩ := hΓ hmem
    have hx : Multiplicative.toAdd ((hmePoint u a s)⁻¹ * ((hmePoint u a s')⁻¹)⁻¹).1
        = ∑ b, ((s' b - s b : ℤ) : ℂ) • u b := by
      simp only [hmePoint, inv_inv, Prod.fst_mul, Prod.fst_inv, toAdd_mul, toAdd_inv, toAdd_ofAdd,
        Int.cast_sub, sub_smul, Finset.sum_sub_distrib]
      abel
    have hy : ∀ i, ((hmePoint u a s)⁻¹ * ((hmePoint u a s')⁻¹)⁻¹).2 i = ∏ b, a b i ^ (s' b - s b) := by
      intro i
      simp only [hmePoint, inv_inv, Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply]
      rw [inv_mul_eq_div, ← Finset.prod_div_distrib]
      simp only [zpow_sub, div_eq_mul_inv]
    rw [hx] at h1
    simp only [hy] at h2
    exact hne (hRinc s' hs' s hs ⟨h1, h2⟩).symm
  have hcopR : Pairwise fun i j : ↥Rₑ => (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))).map (e i.1) ⊔
      (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))).map (e j.1) = ⊤ := by
    intro i j hij
    rw [(he i.1).2.2.2.1, (he j.1).2.2.2.1]
    exact hcop _ _ (hinc i.1 i.2 j.1 j.2 fun h => hij (Subtype.ext h))
  obtain ⟨C₂, hC₂⟩ := exists_card_mul_boxHilb_le_translates (torusBox ℂ A₀ A₁) hmono
    (fun {T U f g} hf hg => hFmul T U f g hf hg) hFfin' hFex (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁)))
    (fun i : ↥Rₑ => e i.1) (fun i T => (he i.1).2.1 T) hcopR
  refine ⟨C₂ + M₀ • CQ, fun t _ => ?_⟩
  have hJsub : torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ}
      ≤ ⨅ i : ↥Rₑ, (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))).map (e i.1) := by
    refine le_iInf fun i => ?_
    rw [(he i.1).2.2.2.1]
    intro f hf
    rw [mem_torusVanishing_iff] at hf ⊢
    intro z hz
    refine hf z ⟨i.1, hR i.1 i.2, z * (hmePoint u a i.1)⁻¹, hz, ?_⟩
    rw [mul_comm z, mul_inv_cancel_left]
  have h1 := box_ray_lower_bound D₀ D₁ H J t
  have h2 := le_boxHilb_torusVanishing_subgroup Γ H J hH hJ (t • boxD A₀ A₁ D₀ D₁)
  have h3 := hC₂ (t • boxD A₀ A₁ D₀ D₁)
  have h4 := boxHilb_anti (torusBox ℂ A₀ A₁) hFfin' hJsub (t • boxD A₀ A₁ D₀ D₁ + C₂)
  have h5 := wustholz_le_boxHilb _ A W M₀ n' hA w hw Q CQ hQbox hQJ hwQ (t • boxD A₀ A₁ D₀ D₁ + C₂)
  rw [hnn] at h5
  rw [Fintype.card_coe] at h3
  have e2 : (∏ h ∈ H, ((t • boxD A₀ A₁ D₀ D₁) (Sum.inl h) + 1)) *
      ∏ j ∈ J, (2 * (t • boxD A₀ A₁ D₀ D₁) (Sum.inr j) + 1)
      = (∏ _h ∈ H, (t * D₀ + 1)) * ∏ _j ∈ J, (2 * (t * D₁) + 1) := by
    simp [boxD]
  rw [e2] at h2
  have hexp : (Fintype.card A₀ + Fintype.card A₁) - (Fintype.card A₀ + Fintype.card A₁ -
      (Module.finrank ℂ ↥V + Module.finrank ℂ ↥L)) = H.card + J.card := by
    have := Finset.card_le_univ H
    have := Finset.card_le_univ J
    rw [hVH, hLJ]
    omega
  rw [hexp, hVH, hLJ, ← add_assoc]
  calc (M₀ + n).choose n * Rₑ.card * D₀ ^ H.card * D₁ ^ J.card * t ^ (H.card + J.card)
      = (M₀ + n).choose n * (Rₑ.card * (t ^ (H.card + J.card) * (D₀ ^ H.card * D₁ ^ J.card))) := by ring
    _ ≤ (M₀ + n).choose n * (Rₑ.card *
          boxHilb (torusBox ℂ A₀ A₁) (torusVanishing (Γ : Set (TorusGroup ℂ A₀ A₁))) (t • boxD A₀ A₁ D₀ D₁)) := by
        gcongr
        exact h1.trans h2
    _ ≤ (M₀ + n).choose n * boxHilb (torusBox ℂ A₀ A₁)
          (torusVanishing {z | ∃ s : B₁ → ℤ, (∀ b, |s b| ≤ (M₁ : ℤ)) ∧ ∃ γ ∈ Γ, z = hmePoint u a s * γ})
          (t • boxD A₀ A₁ D₀ D₁ + C₂) := by
        gcongr
        exact h3.trans h4
    _ ≤ _ := h5
