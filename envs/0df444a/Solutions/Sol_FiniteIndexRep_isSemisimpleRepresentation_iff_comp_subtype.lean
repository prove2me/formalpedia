-- Prove2me | solution 1 for FiniteIndexRep.isSemisimpleRepresentation_iff_comp_subtype
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:53:28.469196+00:00
-- url     : https://prove2.me/submissions/a402e205-21bc-4fc9-bd7e-d417dfe0dcb9

import Mathlib

set_option autoImplicit false

namespace Sol_FiniteIndexRep_isSemisimpleRepresentation_iff_comp_subtype

variable {k G V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Semisimplicity of a monoid representation, in terms of invariant subspaces of `V`. -/
theorem isSemisimple_iff_forall {K : Type*} [Monoid K] (σ : Representation k K V) :
    Representation.IsSemisimpleRepresentation σ ↔
      ∀ W : Submodule k V, (∀ g, ∀ v ∈ W, σ g v ∈ W) →
        ∃ W' : Submodule k V, IsCompl W W' ∧ ∀ g, ∀ v ∈ W', σ g v ∈ W' := by
  constructor
  · intro h W hW
    obtain ⟨b, hb⟩ := h.exists_isCompl ⟨W, fun g v hv => hW g v hv⟩
    refine ⟨b.toSubmodule, IsCompl.of_eq ?_ ?_, fun g v hv => b.apply_mem_toSubmodule g hv⟩
    · exact congrArg Subrepresentation.toSubmodule hb.inf_eq_bot
    · exact congrArg Subrepresentation.toSubmodule hb.sup_eq_top
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨W', hc, hW'⟩ := h a.toSubmodule (fun g v hv => a.apply_mem_toSubmodule g hv)
    refine ⟨⟨W', fun g v hv => hW' g v hv⟩, IsCompl.of_eq ?_ ?_⟩
    · exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
    · exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

variable [Group G] (ρ : Representation k G V)

/-- Every subspace invariant under `S` has an `S`-invariant complement. -/
def CR (S : Set G) : Prop :=
  ∀ W : Submodule k V, (∀ g ∈ S, ∀ v ∈ W, ρ g v ∈ W) →
    ∃ W' : Submodule k V, IsCompl W W' ∧ ∀ g ∈ S, ∀ v ∈ W', ρ g v ∈ W'

theorem isSemisimple_iff_CR_univ :
    Representation.IsSemisimpleRepresentation ρ ↔ CR ρ Set.univ := by
  rw [isSemisimple_iff_forall]
  simp only [CR, Set.mem_univ, true_implies]

theorem isSemisimple_comp_iff_CR (H : Subgroup G) :
    Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) ↔ CR ρ (H : Set G) := by
  rw [isSemisimple_iff_forall]
  simp only [CR, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, Subtype.forall,
    SetLike.mem_coe]

/-- Relative Maschke theorem. -/
theorem relMaschke (K : Subgroup G) [K.FiniteIndex] (hn : (K.index : k) ≠ 0)
    (hK : CR ρ (K : Set G)) : CR ρ Set.univ := by
  intro W hW
  have hW1 : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W := fun g v hv => hW g (Set.mem_univ g) v hv
  obtain ⟨W', hc, hW'⟩ := hK W (fun g _ v hv => hW1 g v hv)
  set p : V →ₗ[k] V := W.projection W' hc with hp_def
  have hp1 : ∀ v, p v ∈ W := fun v => Submodule.projection_apply_mem hc v
  have hp2 : ∀ w ∈ W, p w = w := fun w hw => Submodule.projection_apply_of_mem_left hc hw
  have hp3 : ∀ w ∈ W', p w = 0 := fun w hw => Submodule.projection_apply_of_mem_right hc hw
  have hpK : ∀ g ∈ K, ∀ v, p (ρ g v) = ρ g (p v) := by
    intro g hg v
    have hv : v ∈ W ⊔ W' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, map_add, map_add, hp2 _ (hW1 g w hw), hp3 _ (hW' g (SetLike.mem_coe.mpr hg) w' hw'),
      hp2 w hw, hp3 w' hw', add_zero, add_zero]
  have hwd : ∀ a b : G, a⁻¹ * b ∈ K → ρ b * p * ρ b⁻¹ = ρ a * p * ρ a⁻¹ := by
    intro a b hab
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ K, b = a * l := ⟨a⁻¹ * b, hab, by group⟩
    ext v
    simp only [Module.End.mul_apply, mul_inv_rev, map_mul]
    rw [← hpK l hl, Representation.self_inv_apply]
  let f : G ⧸ K → Module.End k V := fun c =>
    Quotient.liftOn' c (fun g => ρ g * p * ρ g⁻¹)
      (fun a b h => (hwd a b (QuotientGroup.leftRel_apply.mp h)).symm)
  have hf_mk : ∀ g : G, f (g : G ⧸ K) = ρ g * p * ρ g⁻¹ := fun g => rfl
  have hf1 : ∀ c v, f c v ∈ W := by
    intro c v
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [hf_mk]
      exact hW1 g _ (hp1 _)
  have hf2 : ∀ c, ∀ w ∈ W, f c w = w := by
    intro c w hw
    induction c using QuotientGroup.induction_on with
    | H g =>
      rw [hf_mk, Module.End.mul_apply, Module.End.mul_apply, hp2 _ (hW1 g⁻¹ w hw),
        Representation.self_inv_apply]
  have hf3 : ∀ (g : G) c v, f (g • c) (ρ g v) = ρ g (f c v) := by
    intro g c v
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_coe, hf_mk, hf_mk]
      simp only [smul_eq_mul, Module.End.mul_apply, mul_inv_rev, map_mul, Representation.inv_self_apply]
  let _ : Fintype (G ⧸ K) := Fintype.ofFinite _
  let q : Module.End k V := ∑ c : G ⧸ K, f c
  have hq_apply : ∀ v, q v = ∑ c : G ⧸ K, f c v := fun v => LinearMap.sum_apply _ _ _
  have hq1 : ∀ v, q v ∈ W := fun v => by
    rw [hq_apply]; exact Submodule.sum_mem _ fun c _ => hf1 c v
  have hq2 : ∀ w ∈ W, q w = (K.index : k) • w := by
    intro w hw
    rw [hq_apply, Finset.sum_congr rfl (fun c _ => hf2 c w hw), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul k, Fintype.card_eq_nat_card, ← Subgroup.index_eq_card]
  have hq3 : ∀ g v, q (ρ g v) = ρ g (q v) := by
    intro g v
    rw [hq_apply, hq_apply, map_sum]
    symm
    exact Fintype.sum_bijective (g • ·) (MulAction.bijective g) _ _ (fun c => (hf3 g c v).symm)
  let P : V →ₗ[k] W := ((K.index : k)⁻¹ • q).codRestrict W (fun v => W.smul_mem _ (hq1 v))
  have hP : ∀ x : W, P x = x := by
    intro x
    ext
    simp only [P, LinearMap.codRestrict_apply, LinearMap.smul_apply, hq2 x x.2, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  refine ⟨LinearMap.ker P, LinearMap.isCompl_of_proj hP, fun g _ v hv => ?_⟩
  rw [LinearMap.mem_ker] at hv ⊢
  have hv' : ((K.index : k)⁻¹ • q) v = 0 := by
    have := congrArg Subtype.val hv
    simpa [P] using this
  ext
  simp only [P, LinearMap.codRestrict_apply, LinearMap.smul_apply, hq3, ← map_smul] at hv' ⊢
  simp [hv']


/-- Clifford's theorem: the restriction of a finite-dimensional semisimple representation to a
normal subgroup is semisimple. -/
theorem clifford [FiniteDimensional k V] (N : Subgroup G) [hN : N.Normal]
    (hG : CR ρ Set.univ) : CR ρ (N : Set G) := by
  let I : Submodule k V → Prop := fun X => ∀ g ∈ (N : Set G), ∀ v ∈ X, ρ g v ∈ X
  have hI_sup : ∀ X Y, I X → I Y → I (X ⊔ Y) := by
    intro X Y hX hY g hg v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hX g hg x hx) (hY g hg y hy)
  have hI_inf : ∀ X Y, I X → I Y → I (X ⊓ Y) := by
    intro X Y hX hY g hg v hv
    exact ⟨hX g hg v hv.1, hY g hg v hv.2⟩
  have hI_map : ∀ (g : G) X, I X → I (X.map (ρ g)) := by
    intro g X hX n hn v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    have hc : g⁻¹ * n * g⁻¹⁻¹ ∈ N := hN.conj_mem n hn g⁻¹
    refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * n * g⁻¹⁻¹) x, hX _ hc x hx, ?_⟩
    simp only [inv_inv, map_mul, Module.End.mul_apply, Representation.self_inv_apply]
  have hmap_inv : ∀ (g : G) (X : Submodule k V), (X.map (ρ g)).map (ρ g⁻¹) = X := by
    intro g X
    rw [← Submodule.map_comp]
    have : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
      ext v; simp
    rw [this, Submodule.map_id]
  have hmap_inv' : ∀ (g : G) (X : Submodule k V), (X.map (ρ g⁻¹)).map (ρ g) = X := by
    intro g X
    simpa using hmap_inv g⁻¹ X
  let Simple : Submodule k V → Prop := fun X =>
    I X ∧ X ≠ ⊥ ∧ ∀ Y, I Y → Y ≠ ⊥ → Y ≤ X → Y = X
  have hexists : ∀ U, I U → U ≠ ⊥ → ∃ X, Simple X ∧ X ≤ U := by
    intro U hU hU0
    obtain ⟨X, ⟨hX, hX0, hXU⟩, hmin⟩ := (wellFounded_lt (α := Submodule k V)).has_min
      {Y | I Y ∧ Y ≠ ⊥ ∧ Y ≤ U} ⟨U, hU, hU0, le_rfl⟩
    refine ⟨X, ⟨hX, hX0, fun Y hY hY0 hYX => ?_⟩, hXU⟩
    by_contra hne
    exact hmin Y ⟨hY, hY0, hYX.trans hXU⟩ (lt_of_le_of_ne hYX hne)
  have hsimple_map : ∀ (g : G) X, Simple X → Simple (X.map (ρ g)) := by
    rintro g X ⟨hX, hX0, hmin⟩
    refine ⟨hI_map g X hX, ?_, ?_⟩
    · intro h
      apply hX0
      rw [← hmap_inv g X, h, Submodule.map_bot]
    · intro Y hY hY0 hYX
      have h1 : Y.map (ρ g⁻¹) = X := by
        apply hmin _ (hI_map g⁻¹ Y hY)
        · intro h; apply hY0; rw [← hmap_inv' g Y, h, Submodule.map_bot]
        · calc Y.map (ρ g⁻¹) ≤ (X.map (ρ g)).map (ρ g⁻¹) := Submodule.map_mono hYX
            _ = X := hmap_inv g X
      rw [← h1, hmap_inv' g Y]
  set T : Submodule k V := sSup {X | Simple X} with hT
  have hT_inv : ∀ g ∈ (Set.univ : Set G), ∀ v ∈ T, ρ g v ∈ T := by
    intro g _ v hv
    have hle : T ≤ T.comap (ρ g) := by
      apply sSup_le
      intro X hX
      rw [← Submodule.map_le_iff_le_comap]
      exact le_sSup (hsimple_map g X hX)
    exact hle hv
  have hT_top : T = ⊤ := by
    obtain ⟨T', hc, hT'⟩ := hG T hT_inv
    by_cases h0 : T' = ⊥
    · have := hc.sup_eq_top
      rwa [h0, sup_bot_eq] at this
    · exfalso
      obtain ⟨X, hX, hXT'⟩ := hexists T' (fun g _ v hv => hT' g (Set.mem_univ g) v hv) h0
      have hXT : X ≤ T := le_sSup hX
      have hle : X ≤ T ⊓ T' := le_inf hXT hXT'
      rw [hc.inf_eq_bot] at hle
      exact hX.2.1 (le_bot_iff.mp hle)
  intro W hW
  have hbot : I ⊥ := by
    intro g _ v hv
    rw [(Submodule.mem_bot k).mp hv, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨W', ⟨hW'I, hdisj⟩, hmax⟩ := (wellFounded_gt (α := Submodule k V)).has_min
    {Y | I Y ∧ Disjoint W Y} ⟨⊥, hbot, disjoint_bot_right⟩
  have hsup : W ⊔ W' = ⊤ := by
    by_contra hne
    have hnT : ¬ T ≤ W ⊔ W' := by
      rw [hT_top]; exact fun h => hne (top_le_iff.mp h)
    obtain ⟨X, hX, hXn⟩ : ∃ X, Simple X ∧ ¬ X ≤ W ⊔ W' := by
      by_contra hall
      push Not at hall
      exact hnT (sSup_le fun X hX => hall X hX)
    have hdisj2 : Disjoint (W ⊔ W') X := by
      rw [disjoint_iff]
      by_contra h0
      have heq := hX.2.2 ((W ⊔ W') ⊓ X) (hI_inf _ _ (hI_sup _ _ hW hW'I) hX.1) h0 inf_le_right
      exact hXn (heq.symm.le.trans inf_le_left)
    have hd3 : Disjoint W (W' ⊔ X) := hdisj.disjoint_sup_right_of_disjoint_sup_left hdisj2
    apply hmax (W' ⊔ X) ⟨hI_sup _ _ hW'I hX.1, hd3⟩
    exact left_lt_sup.mpr (fun h => hXn (h.trans le_sup_right))
  exact ⟨W', ⟨hdisj, codisjoint_iff.mpr hsup⟩, hW'I⟩

theorem CR_comp_subtype (H : Subgroup G) (S : Set H) (T : Set G)
    (hST : ∀ g : G, g ∈ T ↔ ∃ h ∈ S, (h : G) = g) :
    CR (ρ.comp H.subtype) S ↔ CR ρ T := by
  have hiff : ∀ W : Submodule k V, (∀ h ∈ S, ∀ v ∈ W, (ρ.comp H.subtype) h v ∈ W) ↔
      (∀ g ∈ T, ∀ v ∈ W, ρ g v ∈ W) := by
    intro W
    constructor
    · intro h g hg v hv
      obtain ⟨x, hx, rfl⟩ := (hST g).mp hg
      exact h x hx v hv
    · intro h x hx v hv
      exact h x ((hST x).mpr ⟨x, hx, rfl⟩) v hv
  constructor
  · intro h W hW
    obtain ⟨W', hc, h'⟩ := h W ((hiff W).mpr hW)
    exact ⟨W', hc, (hiff W').mp h'⟩
  · intro h W hW
    obtain ⟨W', hc, h'⟩ := h W ((hiff W).mp hW)
    exact ⟨W', hc, (hiff W').mpr h'⟩

end Sol_FiniteIndexRep_isSemisimpleRepresentation_iff_comp_subtype

open Sol_FiniteIndexRep_isSemisimpleRepresentation_iff_comp_subtype in
theorem solution {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) [H.FiniteIndex] :
    Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) := by
  rw [isSemisimple_iff_CR_univ, isSemisimple_comp_iff_CR]
  constructor
  · intro hG
    have hN : CR ρ (H.normalCore : Set G) := clifford ρ H.normalCore hG
    have hNH : H.normalCore ≤ H := H.normalCore_le
    have hK : CR (ρ.comp H.subtype) ((H.normalCore.subgroupOf H : Subgroup H) : Set H) := by
      rw [CR_comp_subtype ρ H _ (H.normalCore : Set G)]
      · exact hN
      · intro g
        constructor
        · intro hg
          exact ⟨⟨g, hNH hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
        · rintro ⟨h, hh, rfl⟩
          exact Subgroup.mem_subgroupOf.mp hh
    have hH := relMaschke (ρ.comp H.subtype) (H.normalCore.subgroupOf H)
      (Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero) hK
    rw [CR_comp_subtype ρ H _ (H : Set G)] at hH
    · exact hH
    · intro g
      constructor
      · intro hg
        exact ⟨⟨g, hg⟩, Set.mem_univ _, rfl⟩
      · rintro ⟨h, -, rfl⟩
        exact h.2
  · intro hH
    exact relMaschke ρ H (Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero) hH
