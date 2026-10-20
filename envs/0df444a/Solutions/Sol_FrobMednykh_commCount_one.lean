-- Prove2me | solution 1 for FrobMednykh.commCount_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:01:10.147488+00:00
-- url     : https://prove2.me/submissions/d73b72c4-17ba-4a7a-b7bd-b5c128fed2d4

import Mathlib
import Definitions.Def_FrobMednykh_defs

open CategoryTheory
open FrobMednykh
theorem fm_schur {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] (T : V →ₗ[ℂ] V)
    (hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) : ∃ c : ℂ, T = c • LinearMap.id := by
  let f : V ⟶ V := ⟨InducedCategory.homMk (ModuleCat.ofHom T), fun g => by
    ext1
    exact hT g⟩
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id ℂ f
  refine ⟨c, ?_⟩
  have := congrArg (fun φ : V ⟶ V => φ.hom.hom.hom) hc
  exact this.symm.trans rfl

theorem fm_finrank_ne_zero {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] :
    (Module.finrank ℂ V : ℂ) ≠ 0 := by
  intro h
  have h0 : Module.finrank ℂ V = 0 := by exact_mod_cast h
  have hs : Subsingleton V := Module.finrank_zero_iff.mp h0
  apply id_nonzero V
  apply Action.Hom.ext
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact Subsingleton.elim _ _

theorem fm_scalar {G : Type} [Group G] (V : FDRep ℂ G) [Simple V] (T : V →ₗ[ℂ] V)
    (hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T) :
    T = (LinearMap.trace ℂ V T / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, rfl⟩ := fm_schur V T hT
  rw [map_smul, LinearMap.trace_id, smul_eq_mul, mul_div_assoc, div_self (fm_finrank_ne_zero V),
    mul_one]

theorem fm_conj {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) [Simple V]
    (x y : G) :
    ∑ a : G, V.character (a * x * a⁻¹ * y) =
      (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character x * V.character y := by
  set T : V →ₗ[ℂ] V := ∑ a : G, V.ρ (a * x * a⁻¹) with hTdef
  have hT : ∀ g, T ∘ₗ V.ρ g = V.ρ g ∘ₗ T := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hTdef, Finset.sum_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [Equiv.coe_mulLeft, mul_inv_rev]
    group
  have htr : LinearMap.trace ℂ V T = Fintype.card G * V.character x := by
    rw [hTdef, map_sum]
    change ∑ a : G, V.character (a * x * a⁻¹) = _
    simp only [FDRep.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have key := fm_scalar V T hT
  have : ∑ a : G, V.character (a * x * a⁻¹ * y) = LinearMap.trace ℂ V (T ∘ₗ V.ρ y) := by
    rw [← Module.End.mul_eq_comp, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← map_mul]; rfl
  rw [this, key, htr, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul]
  change _ * V.character y = _
  ring

open Classical in
theorem fm_conv {G : Type} [Group G] [Fintype G]
    (V W : FDRep ℂ G) [Simple V] [Simple W] (z : G) :
    ∑ x : G, V.character x * W.character (x⁻¹ * z) =
      if Nonempty (V ≅ W) then (Fintype.card G : ℂ) / Module.finrank ℂ V * V.character z
      else 0 := by
  set S : W →ₗ[ℂ] W := ∑ x : G, V.character x • W.ρ x⁻¹ with hSdef
  have hS : ∀ g, S ∘ₗ W.ρ g = W.ρ g ∘ₗ S := by
    intro g
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hSdef, Finset.sum_mul, Finset.mul_sum]
    rw [← Equiv.sum_comp (MulAut.conj g).toEquiv]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv, MulAut.conj_apply, FDRep.char_conj]
    rw [← map_mul, ← map_mul]
    congr 2
    group
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  have horth := FDRep.char_orthonormal V W
  have htr : LinearMap.trace ℂ W S = ∑ x : G, V.character x * W.character x⁻¹ := by
    rw [hSdef, map_sum]
    simp only [map_smul, smul_eq_mul]; rfl
  have key := fm_scalar W S hS
  have : ∑ x : G, V.character x * W.character (x⁻¹ * z) = LinearMap.trace ℂ W (S ∘ₗ W.ρ z) := by
    rw [← Module.End.mul_eq_comp, hSdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← map_mul]; rfl
  rw [this, key, LinearMap.smul_comp, LinearMap.id_comp, map_smul, smul_eq_mul, htr]
  have hsum : ∑ x : G, V.character x * W.character x⁻¹ =
      (Nat.card G : ℂ) * (if Nonempty (V ≅ W) then 1 else 0) := by
    rw [← horth, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rw [hsum, Nat.card_eq_fintype_card]
  split_ifs with h
  · obtain ⟨i⟩ := h
    rw [FDRep.char_iso i, LinearEquiv.finrank_eq (FDRep.isoToLinearEquiv i)]
    rw [mul_one]; rfl
  · simp

theorem fm_commProd_append {G : Type} [Group G] {m n : ℕ} (x : Fin m → G × G) (y : Fin n → G × G) :
    commProd (Fin.append x y) = commProd x * commProd y := by
  unfold commProd
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    have : (i.castLE (Nat.le_add_right m n)) = Fin.castAdd n i := rfl
    rw [this, Fin.append_left]
  · congr 1
    funext i
    rw [Fin.append_right]

theorem fm_add (G : Type) [Group G] [Fintype G] (g₁ g₂ : ℕ) (w : G) :
    commCount G (g₁ + g₂) w = ∑ σ : G, commCount G g₁ (w * σ⁻¹) * commCount G g₂ σ := by
  classical
  unfold commCount
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e := Fin.appendEquiv (α := G × G) g₁ g₂
  rw [← Finset.card_map ⟨Fin.appendEquiv (α := G × G) g₁ g₂ |>.symm, Equiv.injective _⟩]
  have hset : (Finset.univ.filter (fun x : Fin (g₁ + g₂) → G × G => commProd x = w)).map
      ⟨(Fin.appendEquiv (α := G × G) g₁ g₂).symm, Equiv.injective _⟩ =
      Finset.univ.filter (fun p : (Fin g₁ → G × G) × (Fin g₂ → G × G) =>
        commProd p.1 * commProd p.2 = w) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← fm_commProd_append]
      convert hx
      exact (Fin.appendEquiv g₁ g₂).apply_symm_apply x
    · intro hp
      refine ⟨Fin.appendEquiv g₁ g₂ p, ?_, (Fin.appendEquiv g₁ g₂).symm_apply_apply p⟩
      rw [← hp]
      exact fm_commProd_append p.1 p.2
  rw [hset, Finset.card_eq_sum_card_fiberwise (f := fun p => commProd p.2) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← h1, h2, mul_inv_cancel_right]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, h2, inv_mul_cancel_right]
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

open Classical in
theorem fm_N1 {G : Type} [Group G] [Fintype G] (z : G) :
    (commCount G 1 z : ℂ) = ∑ a : G, ∑ b : G, if a * b * a⁻¹ * b⁻¹ = z then (1 : ℂ) else 0 := by
  unfold commCount
  have e : {x : Fin 1 → G × G // commProd x = z} ≃ {p : G × G // p.1 * p.2 * p.1⁻¹ * p.2⁻¹ = z} :=
    Equiv.subtypeEquiv (Equiv.funUnique (Fin 1) (G × G)) (fun x => by
      simp [commProd, Equiv.funUnique])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rw [← Finset.univ_product_univ, Finset.sum_product]

theorem fm_N1_inv {G : Type} [Group G] [Fintype G] (z : G) :
    (commCount G 1 z : ℂ) = commCount G 1 z⁻¹ := by
  rw [fm_N1, fm_N1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  apply propext
  constructor
  · intro h; rw [← h]; group
  · intro h; rw [← inv_inv z, ← h]; group

open Classical in
theorem fm_delta {G ι : Type} [Group G] [Fintype G] [Fintype ι] (B : IrrepFamily G ι) (w z : G) :
    (if w = z then (1 : ℂ) else 0) =
      ∑ i, (Fintype.card G : ℂ)⁻¹ * (B.dim i : ℂ) * (B.V i).character (w * z⁻¹) := by
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [fm_sum_dim B]
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  by_cases h : w = z
  · rw [if_pos h, if_pos (by rw [h, mul_inv_cancel]), inv_mul_cancel₀ hc]
  · rw [if_neg h, if_neg (fun h' => h (mul_inv_eq_one.mp h')), mul_zero]

theorem fm_one_inv {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    (commCount G 1 z : ℂ) = Fintype.card G * ∑ i, (B.V i).character z⁻¹ / B.dim i := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [fm_N1]
  simp only [fm_delta B]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := B.simple i
  have hd : (B.dim i : ℂ) ≠ 0 := fm_finrank_ne_zero (B.V i)
  have h1 : ∀ b : G, ∑ a : G, (Fintype.card G : ℂ)⁻¹ * B.dim i *
      (B.V i).character (a * b * a⁻¹ * b⁻¹ * z⁻¹) =
      (Fintype.card G : ℂ)⁻¹ * B.dim i *
        (Fintype.card G / B.dim i * (B.V i).character b * (B.V i).character (b⁻¹ * z⁻¹)) := by
    intro b
    rw [← Finset.mul_sum]
    congr 1
    have := fm_conj (B.V i) b (b⁻¹ * z⁻¹)
    simp only [mul_assoc] at this ⊢
    exact this
  rw [Finset.sum_congr rfl (fun b _ => h1 b), ← Finset.mul_sum]
  have h2 := fm_conv (B.V i) (B.V i) z⁻¹
  rw [if_pos ⟨Iso.refl _⟩] at h2
  have h3 : ∑ b : G, (Fintype.card G : ℂ) / B.dim i * (B.V i).character b *
      (B.V i).character (b⁻¹ * z⁻¹) =
      (Fintype.card G : ℂ) / B.dim i * ∑ b : G, (B.V i).character b * (B.V i).character (b⁻¹ * z⁻¹) := by
    rw [Finset.mul_sum]; simp only [mul_assoc]
  rw [h3, h2]
  unfold IrrepFamily.dim at hd ⊢
  field_simp

theorem fm_one {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    (commCount G 1 z : ℂ) = Fintype.card G * ∑ i, (B.V i).character z / B.dim i := by
  rw [fm_N1_inv, fm_one_inv B, inv_inv]

theorem solution {G ι : Type} [Group G] [Fintype G] [Fintype ι]
    (B : IrrepFamily G ι) (z : G) :
    (commCount G 1 z : ℂ) = Fintype.card G * ∑ i, (B.V i).character z / B.dim i := by
  exact fm_one B z


