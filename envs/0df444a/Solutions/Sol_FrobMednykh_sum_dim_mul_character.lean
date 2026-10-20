-- Prove2me | solution 1 for FrobMednykh.sum_dim_mul_character
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T19:58:44.023632+00:00
-- url     : https://prove2.me/submissions/97f5bb72-9414-479e-bbda-66cdf7e91c37

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_trace_compl {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (K K' : Submodule ℂ V) (hc : IsCompl K K') (f : V →ₗ[ℂ] V) (hK : ∀ v ∈ K, f v ∈ K)
    (hK' : ∀ v ∈ K', f v ∈ K') :
    LinearMap.trace ℂ V f = LinearMap.trace ℂ K (f.restrict hK) + LinearMap.trace ℂ K' (f.restrict hK') := by
  let N : Bool → Submodule ℂ V := fun b => cond b K K'
  have hN : DirectSum.IsInternal N := by
    rw [DirectSum.isInternal_submodule_iff_isCompl N (i := true) (j := false) (by decide)
      (by ext b; cases b <;> simp)]
    exact hc
  have hf : ∀ b, Set.MapsTo f (N b) (N b) := by
    intro b; cases b
    · exact fun v hv => hK' v hv
    · exact fun v hv => hK v hv
  rw [LinearMap.trace_eq_sum_trace_restrict hN hf, Fintype.sum_bool]
  rfl

theorem fm_regular_char {G : Type} [Group G] [Fintype G] [DecidableEq G] (z : G) :
    (FDRep.of (TannakaDuality.FiniteGroup.leftRegular (k := ℂ) (G := G))).character z =
      if z = 1 then (Fintype.card G : ℂ) else 0 := by
  change LinearMap.trace ℂ (G → ℂ) (TannakaDuality.FiniteGroup.leftRegular z) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    TannakaDuality.FiniteGroup.leftRegular_apply]
  split_ifs with h
  · subst h; simp
  · apply Finset.sum_eq_zero
    intro t _
    rw [Pi.single_apply, if_neg]
    intro ht
    apply h
    have := congrArg (fun u => t * u⁻¹) ht
    simpa using this
theorem fm_split {G : Type} [Group G] [Fintype G] (X : FDRep ℂ G)
    (hX : 0 < Module.finrank ℂ X) (hs : ¬ Simple X) :
    ∃ K K' : Submodule ℂ X, IsCompl K K' ∧ K ≠ ⊥ ∧ K' ≠ ⊥ ∧
      (∀ g, ∀ v ∈ K, X.ρ g v ∈ K) ∧ (∀ g, ∀ v ∈ K', X.ρ g v ∈ K') := by
  have hne : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  have : NeZero (Nat.card G : ℂ) := ⟨hne⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by rwa [Nat.card_eq_fintype_card] at hne
  have hfr : Module.finrank ℂ (X ⟶ X) ≠ 1 := fun h => hs ((FDRep.simple_iff_end_is_rank_one X).mpr h)
  have hnt : Nontrivial X := Module.finrank_pos_iff.mp hX
  obtain ⟨v0, hv0⟩ := exists_ne (0 : X)
  have h1 : 𝟙 X ≠ 0 := by
    intro h
    have := congrArg (fun φ : X ⟶ X => φ.hom.hom.hom v0) h
    exact hv0 this
  obtain ⟨f, hf⟩ : ∃ f : X ⟶ X, ∀ c : ℂ, c • 𝟙 X ≠ f := by
    by_contra hc
    push Not at hc
    exact hfr ((finrank_eq_one_iff_of_nonzero' _ h1).mpr hc)
  set F : X →ₗ[ℂ] X := f.hom.hom.hom with hFdef
  have hF : ∀ g, F ∘ₗ X.ρ g = X.ρ g ∘ₗ F := fun g => congrArg (fun φ => φ.hom.hom) (f.comm g)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue F
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  set H : X →ₗ[ℂ] X := F - μ • LinearMap.id with hHdef
  have hH : ∀ g w, H (X.ρ g w) = X.ρ g (H w) := by
    intro g w
    have := LinearMap.congr_fun (hF g) w
    simp only [LinearMap.comp_apply] at this
    simp [hHdef, this]
  set K := LinearMap.ker H with hKdef
  have hKinv : ∀ g, ∀ w ∈ K, X.ρ g w ∈ K := by
    intro g w hw
    rw [hKdef, LinearMap.mem_ker] at hw ⊢
    rw [hH, hw, map_zero]
  have hvK : v ∈ K := by
    rw [hKdef, LinearMap.mem_ker, hHdef, LinearMap.sub_apply, hv.apply_eq_smul]
    simp
  have hKbot : K ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Submodule ℂ X) := h ▸ hvK
    exact hv.2 ((Submodule.mem_bot ℂ).mp this)
  have hKtop : K ≠ ⊤ := by
    intro h
    apply hf μ
    have hH0 : H = 0 := by
      ext w
      have : w ∈ K := h ▸ Submodule.mem_top
      exact this
    apply Action.Hom.ext
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    have := LinearMap.congr_fun hH0 w
    simp only [hHdef, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero] at this
    exact this.symm.trans rfl
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  let π : X →ₗ[ℂ] K := Submodule.linearProjOfIsCompl K C hC
  let R : G → (K →ₗ[ℂ] K) := fun g => (X.ρ g).restrict (hKinv g)
  let P : X →ₗ[ℂ] K := (Fintype.card G : ℂ)⁻¹ • ∑ g : G, R g ∘ₗ π ∘ₗ X.ρ g⁻¹
  have hP : ∀ x : K, P x = x := by
    intro x
    have hterm : ∀ g, (R g ∘ₗ π ∘ₗ X.ρ g⁻¹) x = x := by
      intro g
      apply Subtype.ext
      have hx : X.ρ g⁻¹ x ∈ K := hKinv g⁻¹ x x.2
      simp only [LinearMap.comp_apply, R, LinearMap.restrict_apply]
      have : π (X.ρ g⁻¹ x) = ⟨X.ρ g⁻¹ x, hx⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hC ⟨_, hx⟩
      rw [this]
      simp [← Module.End.mul_apply, ← map_mul]
    simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, hterm,
      Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hPeq : ∀ h w, P (X.ρ h w) = R h (P w) := by
    intro h w
    simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
      map_sum, LinearMap.comp_apply]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulLeft h)]
    refine Finset.sum_congr rfl fun g _ => ?_
    apply Subtype.ext
    simp only [Equiv.coe_mulLeft, R, LinearMap.restrict_apply, mul_inv_rev]
    rw [← Module.End.mul_apply (X.ρ (g⁻¹ * h⁻¹)), ← map_mul, inv_mul_cancel_right]
    rw [← Module.End.mul_apply (X.ρ h), ← map_mul]
  refine ⟨K, LinearMap.ker P, LinearMap.isCompl_of_proj hP, hKbot, ?_, hKinv, ?_⟩
  · intro h
    apply hKtop
    have := LinearMap.isCompl_of_proj hP
    rw [h] at this
    exact codisjoint_bot.mp this.codisjoint
  · intro g w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hPeq, hw, map_zero]

theorem fm_sub_char {G : Type} [Group G] (X : FDRep ℂ G) (K : Submodule ℂ X)
    (hK : ∀ g, ∀ v ∈ K, X.ρ g v ∈ K) (g : G) :
    (FDRep.of (Representation.subrepresentation X.ρ K (fun g v hv => hK g v hv))).character g =
      LinearMap.trace ℂ K ((X.ρ g).restrict (hK g)) := rfl

theorem fm_span {G ι : Type} [Group G] [Fintype G] [Fintype ι] (B : IrrepFamily G ι) :
    ∀ n (X : FDRep ℂ G), Module.finrank ℂ X = n →
      X.character ∈ Submodule.span ℂ (Set.range fun i => (B.V i).character) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hn
  by_cases h0 : n = 0
  · have : Subsingleton X := Module.finrank_zero_iff.mp (hn.trans h0)
    have hz : X.character = 0 := by
      funext g
      have : X.ρ g = 0 := Subsingleton.elim _ _
      change LinearMap.trace ℂ X (X.ρ g) = 0
      rw [this, map_zero]
    rw [hz]; exact Submodule.zero_mem _
  by_cases hs : Simple X
  · obtain ⟨i, ⟨e⟩⟩ := B.complete X hs
    rw [FDRep.char_iso e]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨K, K', hc, hK, hK', hKi, hKi'⟩ := fm_split X (by omega) hs
  have hsum : X.character =
      (FDRep.of (Representation.subrepresentation X.ρ K (fun g v hv => hKi g v hv))).character +
      (FDRep.of (Representation.subrepresentation X.ρ K' (fun g v hv => hKi' g v hv))).character := by
    funext g
    rw [Pi.add_apply, fm_sub_char, fm_sub_char]
    exact fm_trace_compl K K' hc (X.ρ g) (hKi g) (hKi' g)
  have hKt : K ≠ ⊤ := fun h => hK' (by
    rw [h] at hc; exact hc.symm.disjoint.eq_bot_of_le le_top)
  have hKt' : K' ≠ ⊤ := fun h => hK (by
    rw [h] at hc; exact hc.disjoint.eq_bot_of_le le_top)
  rw [hsum]
  apply Submodule.add_mem
  · exact ih _ (hn ▸ Submodule.finrank_lt hKt) _ rfl
  · exact ih _ (hn ▸ Submodule.finrank_lt hKt') _ rfl

theorem fm_sum_dim {G ι : Type} [Group G] [Fintype G] [DecidableEq G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    ∑ i, (B.dim i : ℂ) * (B.V i).character z = if z = 1 then (Fintype.card G : ℂ) else 0 := by
  classical
  let Rg := FDRep.of (TannakaDuality.FiniteGroup.leftRegular (k := ℂ) (G := G))
  have hsp := fm_span B _ Rg rfl
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hsp
  have hne : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hne
  have hcj : ∀ j, c j = B.dim j := by
    intro j
    have := B.simple j
    have h1 := congrArg (fun f : G → ℂ => ∑ g : G, f g * (B.V j).character g⁻¹) hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul] at h1
    rw [Finset.sum_comm] at h1
    have hpair : ∀ i, ∑ g : G, c i * (B.V i).character g * (B.V j).character g⁻¹ =
        if i = j then c i * Nat.card G else 0 := by
      intro i
      have := B.simple i
      have ho := FDRep.char_orthonormal (B.V i) (B.V j)
      simp only [mul_assoc, ← Finset.mul_sum]
      have h2 : ∑ g : G, (B.V i).character g * (B.V j).character g⁻¹ =
          (Nat.card G : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G, (B.V i).character g * (B.V j).character g⁻¹) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
      rw [h2, ho]
      by_cases hij : i = j
      · subst hij; rw [if_pos ⟨Iso.refl _⟩, if_pos rfl]; simp
      · rw [if_neg (fun ⟨e⟩ => hij (B.injective i j ⟨e⟩)), if_neg hij]; simp
    simp only [hpair, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have hreg : ∑ g : G, Rg.character g * (B.V j).character g⁻¹ = Nat.card G * B.dim j := by
      simp only [Rg, fm_regular_char, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true, inv_one, FDRep.char_one, IrrepFamily.dim, Nat.card_eq_fintype_card]
    rw [hreg] at h1
    have := mul_right_cancel₀ hne (h1.trans (mul_comm _ _))
    exact this
  have := congrFun hc z
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcj] at this
  rw [this, fm_regular_char]

theorem solution {G ι : Type} [Group G] [Fintype G] [DecidableEq G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    ∑ i, (B.dim i : ℂ) * (B.V i).character z = if z = 1 then (Fintype.card G : ℂ) else 0 := by
  exact fm_sum_dim B z


