-- Prove2me | solution 1 for Formalism.HN.slopeIneq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:16:16.817644+00:00
-- url     : https://prove2.me/submissions/c7a14de0-46d2-452e-b6fd-3a0ad33576db

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
import Theorems.Thm_Formalism_HN_rank_range_eq_and_degree_le
import Theorems.Thm_Formalism_HN_norm_starProjection_le
import Theorems.Thm_Formalism_HN_range_comp_eq_imageLattice
import Theorems.Thm_Formalism_HN_map_range_toIntLinearMap
import Theorems.Thm_Formalism_HN_eq_zero_of_injOn
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_F_saturProps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section SlopeTestRemainingChoices
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
end SlopeTestRemainingChoices
universe uR uV uW uE uF
private lemma mem_of_starProjection_orthogonal_eq_zero {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (K : Submodule ℝ X) (x : X) (h : Kᗮ.starProjection x = 0) :
    x ∈ K := by
  have hw : x - Kᗮ.starProjection x ∈ K := by
    first
    | exact (Submodule.orthogonal_orthogonal K) ▸
        Submodule.sub_starProjection_mem_orthogonal (K := Kᗮ) x
    | (have hd := Submodule.starProjection_add_starProjection_orthogonal (K := K) x
       rw [sub_eq_of_eq_add hd.symm]
       first
       | exact Submodule.starProjection_apply_mem _ _
       | exact (K.orthogonalProjection x).2
       | simp)
  rwa [h, sub_zero] at hw
private theorem slopeIneq_of_lemma {R V W E F : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : V →+ E) (ρ' : W →+ F) (L : Submodule R V) (M : Submodule R W) (hL : IsLat ρ L)
    (hM : IsLat ρ' M) (φ : L →ₗ[R] M) (C : ℝ) (hC : 0 < C)
    (hφC : ∀ x : L, ‖ρ' (φ x : W)‖ ≤ C * ‖ρ (x : V)‖) (N : Submodule R V) (hNL : N ≤ L)
    (hinj : ∀ x : L, (x : V) ∈ N → φ x = 0 → x = 0) (N' : Submodule R W)
    (hN' : ∀ w, w ∈ N' ↔ ∃ x : L, (x : V) ∈ N ∧ (φ x : W) = w)
    (hN : IsLat ρ N) (hN'l : IsLat ρ' N') :
    rk ρ' N' = rk ρ N ∧ deg ρ N - (rk ρ N : ℝ) * Real.log C ≤ deg ρ' N' := by
  let j : ↥(N.comap L.subtype) →+ V :=
    (L.subtype ∘ₗ (N.comap L.subtype).subtype).toAddMonoidHom
  let j' : ↥(N.comap L.subtype) →+ W :=
    (M.subtype ∘ₗ φ ∘ₗ (N.comap L.subtype).subtype).toAddMonoidHom
  have hj : ∀ v, v ∈ N ↔ ∃ g, j g = v := by
    intro v
    constructor
    · intro hv
      exact ⟨⟨⟨v, hNL hv⟩, hv⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact g.2
  have hj' : ∀ w, w ∈ N' ↔ ∃ g, j' g = w := by
    intro w
    rw [hN']
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, g.2, rfl⟩
  have eA := range_comp_eq_imageLattice ρ N j hj
  have eB := range_comp_eq_imageLattice ρ' N' j' hj'
  haveI : DiscreteTopology (LinearMap.range (ρ.comp j).toIntLinearMap) := by
    rw [eA]; exact hN.2
  haveI : DiscreteTopology (LinearMap.range (ρ'.comp j').toIntLinearMap) := by
    rw [eB]; exact hN'l.2
  have hz : ∀ g : ↥(N.comap L.subtype), ρ (j g) = 0 → g = 0 := by
    intro g hg
    have h1 : ((g : L) : V) = 0 := eq_zero_of_injOn hL.1 (g : L).2 hg
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  have hz' : ∀ g : ↥(N.comap L.subtype), ρ' (j' g) = 0 → g = 0 := by
    intro g hg
    have h1 : ((φ (g : L) : M) : W) = 0 := eq_zero_of_injOn hM.1 (φ (g : L)).2 hg
    have h2 : φ (g : L) = 0 := Subtype.ext (by simpa using h1)
    have h3 := hinj (g : L) g.2 h2
    apply Subtype.ext
    simpa using h3
  have hR := rank_range_eq_and_degree_le (ρ.comp j) (ρ'.comp j')
    (fun g hg => by rw [hz g hg, map_zero])
    (fun g hg => by rw [hz' g hg, map_zero]) C hC (fun g => hφC (g : L))
  rw [eA, eB] at hR
  exact hR
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe uR uV uW uE uF
namespace Formalism.HN
theorem _root_.solution (hmV : MuChar.{uR, uV, uE}) (hmW : MuChar.{uR, uW, uF})
    (hs : SatR.{uR, uW, uF}) (hbV : SatBasic.{uR, uV, uE}) (hbW : SatBasic.{uR, uW, uF}) :
    SlopeIneq.{uR, uV, uW, uE, uF} := by
  intro R V W E F _ _ _ _ _ _ _ _ _ _ _ ρ ρ' L M hL hM φ C hC hφC
  have hbL := hbV R V E ρ L hL
  have hbM := hbW R W F ρ' M hM
  have zmono : ∀ {A B : Submodule R W}, A ≤ B → zl ρ' A ≤ zl ρ' B := by
    intro A B hAB x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, hAB hv, rfl⟩
  have zmonoV : ∀ {A B : Submodule R V}, A ≤ B → zl ρ A ≤ zl ρ B := by
    intro A B hAB x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, hAB hv, rfl⟩
  have zmem : ∀ {A : Submodule R W} {w : W}, w ∈ A → ρ' w ∈ zl ρ' A := fun hw => ⟨_, hw, rfl⟩
  have zmemV : ∀ {A : Submodule R V} {v : V}, v ∈ A → ρ v ∈ zl ρ A := fun hv => ⟨_, hv, rfl⟩
  have hMuM : M ≠ ⊥ → ∀ N : Submodule R W, N ≤ M → deg ρ' N ≤ muMax ρ' M * rk ρ' N :=
    fun hM0 => ((hmW R W F ρ' M hM hM0).1 (muMax ρ' M)).1 le_rfl
  obtain ⟨Im, hIm⟩ : ∃ Im : Submodule R W, Im = (LinearMap.range φ).map M.subtype := ⟨_, rfl⟩
  rw [← hIm]
  have hImM : Im ≤ M := by
    rw [hIm]; rintro _ ⟨y, _, rfl⟩; exact y.2
  have hImmem : ∀ g : L, (φ g : W) ∈ Im := fun g => by
    rw [hIm]; exact ⟨φ g, ⟨g, rfl⟩, rfl⟩
  have hImLat : IsLat ρ' Im := hbM.1 _ hImM
  have hbIm := hbW R W F ρ' Im hImLat
  refine ⟨fun hφ0 => ?_, fun hinj hL0 => ?_⟩
  · have hIm0 : Im ≠ ⊥ := by
      intro h0
      apply hφ0
      ext x
      have h1 := (Submodule.eq_bot_iff Im).1 h0 _ (hImmem x)
      simpa using h1
    have hM0 : M ≠ ⊥ := by
      intro h0
      apply hIm0
      rw [Submodule.eq_bot_iff]
      intro w hw
      exact (Submodule.eq_bot_iff M).1 h0 w (hImM hw)
    have hL0 : L ≠ ⊥ := by
      intro h0
      apply hφ0
      ext x
      have h1 : x = 0 := Subtype.ext ((Submodule.eq_bot_iff L).1 h0 _ x.2)
      simp [h1]
    have muL := hmV R V E ρ L hL hL0
    have muIm := hmW R W F ρ' Im hImLat hIm0
    have h1a : muMin ρ L - Real.log C ≤ muMin ρ' Im := by
      refine (muIm.2.1 _).2 ?_
      intro N' hN'
      obtain ⟨N'', h1, h2, h3⟩ := hs R W F ρ' Im N' hImLat hN'
      have sp := Formalism.F.saturProps F (zl ρ' Im) (zl ρ' N') hImLat.2 (zmono hN')
      rw [← h3] at sp
      have hdeg : deg ρ' N' ≤ deg ρ' N'' := (hbIm.2.1 N' N'' h1 h2).2 sp.2.2.symm
      obtain ⟨N, hNdef⟩ : ∃ N : Submodule R V,
          N = (N''.comap (M.subtype ∘ₗ φ)).map L.subtype := ⟨_, rfl⟩
      have hNmem : ∀ g : L, (g : V) ∈ N ↔ (φ g : W) ∈ N'' := by
        intro g
        rw [hNdef]
        constructor
        · rintro ⟨x, hx, hxg⟩
          have hxg' : x = g := Subtype.ext hxg
          subst hxg'
          exact hx
        · intro h
          exact ⟨g, h, rfl⟩
      have hNL : N ≤ L := by
        rw [hNdef]; rintro _ ⟨x, _, rfl⟩; exact x.2
      have hkey : ∀ g : L, ρ' (φ g : W) ∈ span ℝ (zl ρ' N'' : Set F) → (g : V) ∈ N := by
        intro g hg
        have h4 := sp.1.2 _ (zmem (hImmem g)) hg
        obtain ⟨w, hw, hwg⟩ := h4
        have h5 : w = (φ g : W) := hM.1 (hImM (h2 hw)) (φ g).2 hwg
        rw [hNmem, ← h5]
        exact hw
      let α0 : L →+ E := ρ.comp L.subtype.toAddMonoidHom
      let β0 : L →+ F := ρ'.comp (M.subtype ∘ₗ φ).toAddMonoidHom
      have hαS : α0 '' {g : L | (g : V) ∈ N} = (zl ρ N : Set E) := by
        ext y
        constructor
        · rintro ⟨g, hg, rfl⟩
          exact ⟨g, hg, rfl⟩
        · rintro ⟨v, hv, rfl⟩
          exact ⟨⟨v, hNL hv⟩, hv, rfl⟩
      have hSU : ∀ s ∈ {g : L | (g : V) ∈ N}, β0 s ∈ span ℝ (zl ρ' N'' : Set F) := by
        intro s hs'
        exact Submodule.subset_span (zmem ((hNmem s).1 hs'))
      have hproj : ∀ g : L, ‖(span ℝ (zl ρ' N'' : Set F))ᗮ.starProjection (β0 g)‖ ≤
          C * ‖(span ℝ (zl ρ N : Set E))ᗮ.starProjection (α0 g)‖ := by
        intro g
        have := norm_starProjection_le α0 β0 C (fun g => hφC g) _ _ hSU g
        rwa [hαS] at this
      have hkeyE : ∀ g : L, ρ (g : V) ∈ span ℝ (zl ρ N : Set E) → (g : V) ∈ N := by
        intro g hg
        apply hkey
        apply mem_of_starProjection_orthogonal_eq_zero
        have h6 := hproj g
        have h7 : (span ℝ (zl ρ N : Set E))ᗮ.starProjection (α0 g) = 0 :=
          starProjection_orthogonal_apply_eq_zero hg
        rw [h7, norm_zero, mul_zero] at h6
        exact norm_le_zero_iff.mp h6
      have hsatN : Formalism.F.IsSaturated (zl ρ L) (zl ρ N) := by
        refine ⟨zmonoV hNL, ?_⟩
        intro x hx hxs
        obtain ⟨v, hv, rfl⟩ := hx
        exact zmemV (hkeyE ⟨v, hv⟩ hxs)
      let pE : E →L[ℝ] E := (span ℝ (zl ρ N : Set E))ᗮ.starProjection
      let pF : F →L[ℝ] F := (span ℝ (zl ρ' N'' : Set F))ᗮ.starProjection
      have hαβ : ∀ g, (pE.toLinearMap.toAddMonoidHom.comp α0) g = 0 →
          (pF.toLinearMap.toAddMonoidHom.comp β0) g = 0 := by
        intro g hg
        have hgN := hkeyE g (mem_of_starProjection_orthogonal_eq_zero (span ℝ (zl ρ N : Set E)) (ρ (g : V)) hg)
        exact starProjection_orthogonal_apply_eq_zero
          (Submodule.subset_span (zmem ((hNmem g).1 hgN)))
      have hβα : ∀ g, (pF.toLinearMap.toAddMonoidHom.comp β0) g = 0 →
          (pE.toLinearMap.toAddMonoidHom.comp α0) g = 0 := by
        intro g hg
        have hgN := hkey g (mem_of_starProjection_orthogonal_eq_zero (span ℝ (zl ρ' N'' : Set F)) (ρ' (φ g : W)) hg)
        exact starProjection_orthogonal_apply_eq_zero (Submodule.subset_span (zmemV hgN))
      have hzlL : LinearMap.range α0.toIntLinearMap = zl ρ L :=
        range_comp_eq_imageLattice ρ L L.subtype.toAddMonoidHom (fun v =>
          ⟨fun hv => ⟨⟨v, hv⟩, rfl⟩, by rintro ⟨g, rfl⟩; exact g.2⟩)
      have hzlIm : LinearMap.range β0.toIntLinearMap = zl ρ' Im :=
        range_comp_eq_imageLattice ρ' Im (M.subtype ∘ₗ φ).toAddMonoidHom (fun w => by
          rw [hIm]
          constructor
          · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
            exact ⟨x, rfl⟩
          · rintro ⟨x, rfl⟩
            exact ⟨φ x, ⟨x, rfl⟩, rfl⟩)
      have eQL : LinearMap.range (pE.toLinearMap.toAddMonoidHom.comp α0).toIntLinearMap =
          Formalism.F.quot (zl ρ L) (zl ρ N) := by
        rw [← map_range_toIntLinearMap, hzlL]
        rfl
      have eQM : LinearMap.range (pF.toLinearMap.toAddMonoidHom.comp β0).toIntLinearMap =
          Formalism.F.quot (zl ρ' Im) (zl ρ' N'') := by
        rw [← map_range_toIntLinearMap, hzlIm]
        rfl
      have hsatQ := Formalism.F.degQuot E (zl ρ L) (zl ρ N) hL.2 hsatN
      have hsatQ' := Formalism.F.degQuot F (zl ρ' Im) (zl ρ' N'') hImLat.2 sp.1
      haveI : DiscreteTopology
          (LinearMap.range (pE.toLinearMap.toAddMonoidHom.comp α0).toIntLinearMap) := by
        rw [eQL]; exact hsatQ.1
      haveI : DiscreteTopology
          (LinearMap.range (pF.toLinearMap.toAddMonoidHom.comp β0).toIntLinearMap) := by
        rw [eQM]; exact hsatQ'.1
      have hR := rank_range_eq_and_degree_le (pE.toLinearMap.toAddMonoidHom.comp α0)
        (pF.toLinearMap.toAddMonoidHom.comp β0) hαβ hβα C hC (fun g => hproj g)
      rw [eQL, eQM] at hR
      have q1 := hbL.2.2.2.2.2.2.2 N ⟨hNL, hsatN⟩
      have q2 := hbIm.2.2.2.2.2.2.2 N'' ⟨h2, sp.1⟩
      have MuL := (muL.2.1 (muMin ρ L)).1 le_rfl N hNL
      have c1 : (Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N)) : ℝ) = (rk ρ L : ℝ) - rk ρ N := by
        rw [q1.1, Nat.cast_sub q1.2.1]
      have c2 : (Formalism.F.rk (Formalism.F.quot (zl ρ' Im) (zl ρ' N'')) : ℝ) =
          (rk ρ' Im : ℝ) - rk ρ' N'' := by
        rw [q2.1, Nat.cast_sub q2.2.1]
      have c3 : (Formalism.F.rk (Formalism.F.quot (zl ρ' Im) (zl ρ' N'')) : ℝ) =
          Formalism.F.rk (Formalism.F.quot (zl ρ L) (zl ρ N)) := congrArg (Nat.cast : ℕ → ℝ) hR.1
      have c4 : (rk ρ' N'' : ℝ) = rk ρ' N' := congrArg (Nat.cast : ℕ → ℝ) sp.2.2
      rw [← c4, ← c2, c3]
      rw [← c1] at MuL
      have d1 := q1.2.2
      have d2 := q2.2.2
      have d3 := hR.2
      nlinarith
    refine ⟨h1a, ?_⟩
    have hImMax : muMax ρ' Im ≤ muMax ρ' M :=
      (muIm.1 (muMax ρ' M)).2 (fun N hN => hMuM hM0 N (hN.trans hImM))
    have e1 := muIm.2.2.2.1
    have e2 := muIm.2.2.2.2
    linarith
  · have hM0 : M ≠ ⊥ := by
      intro h0
      apply hL0
      rw [Submodule.eq_bot_iff]
      intro v hv
      have h1 : φ ⟨v, hv⟩ = φ 0 := by
        rw [map_zero]
        exact Subtype.ext ((Submodule.eq_bot_iff M).1 h0 _ (φ ⟨v, hv⟩).2)
      have h2 := congrArg Subtype.val (hinj h1)
      simpa using h2
    refine ((hmV R V E ρ L hL hL0).1 _).2 ?_
    intro N hN
    obtain ⟨N', hN'mem⟩ : ∃ N' : Submodule R W,
        ∀ w, w ∈ N' ↔ ∃ x : L, (x : V) ∈ N ∧ (φ x : W) = w :=
      ⟨(N.comap L.subtype).map (M.subtype ∘ₗ φ), fun w => by
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩⟩
    have hN'M : N' ≤ M := fun w hw => by
      obtain ⟨x, _, rfl⟩ := (hN'mem w).1 hw
      exact (φ x).2
    have key := slopeIneq_of_lemma ρ ρ' L M hL hM φ C hC hφC N hN
      (fun x _ h => hinj (h.trans (map_zero φ).symm)) N' hN'mem (hbL.1 N hN) (hbM.1 N' hN'M)
    have h3 := hMuM hM0 N' hN'M
    rw [key.1] at h3
    nlinarith [key.2]
end Formalism.HN
