-- Prove2me | solution 1 for Formalism.HN.hnSum_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:36.903708+00:00
-- url     : https://prove2.me/submissions/10d34a7e-7990-46e3-a67a-621caf0b29c3

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Theorems.Thm_Formalism_HN_hnSum_isLat_mono
import Theorems.Thm_Formalism_HN_hnSum_orth
import Theorems.Thm_Formalism_HN_hnSum_orth_rk
import Theorems.Thm_Formalism_HN_hnSum_split
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
section
variable {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ρ : V →+ E)
variable [FiniteDimensional ℝ E]
end
universe u v w x
section
variable {R : Type u} {V : Type v} {E : Type w} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ρ : V →+ E)
end
private theorem le_muMin_sup_of_le_muMin {R : Type u} {V : Type v} {E : Type w} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (ρ : V →+ E)
    {L A B : Submodule R V} (hL : IsLat ρ L) (hA : A ≤ L) (hB : B ≤ L) (hA0 : A ≠ ⊥)
    (hB0 : B ≠ ⊥) {θ : ℝ} (hθA : θ ≤ muMin ρ A) (hθB : θ ≤ muMin ρ B) :
    θ ≤ muMin ρ (A ⊔ B) := by
  have hAl : IsLat ρ A := hnSum_isLat_mono ρ hL hA
  have hBl : IsLat ρ B := hnSum_isLat_mono ρ hL hB
  have hM : A ⊔ B ≤ L := sup_le hA hB
  have hMl : IsLat ρ (A ⊔ B) := hnSum_isLat_mono ρ hL hM
  have hM0 : A ⊔ B ≠ ⊥ := fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
  rw [(h2 R V E ρ (A ⊔ B) hMl hM0).2.1 θ]
  intro N hN
  have eA := ((h2 R V E ρ A hAl hA0).2.1 θ).1 hθA (N ⊓ A) inf_le_right
  have eB := ((h2 R V E ρ B hBl hB0).2.1 θ).1 hθB (B ⊓ (N ⊔ A)) inf_le_left
  have hNA : N ⊔ A ≤ L := sup_le (hN.trans hM) hA
  have s1 := h1 R V E ρ L N A hL (hN.trans hM) hA
  have s2 := h1 R V E ρ L B (N ⊔ A) hL hB hNA
  have hBNA : B ⊔ (N ⊔ A) = A ⊔ B :=
    le_antisymm (sup_le le_sup_right (sup_le hN le_sup_left))
      (sup_le ((le_sup_right : A ≤ N ⊔ A).trans le_sup_right) le_sup_left)
  rw [hBNA] at s2
  obtain ⟨r1, d1⟩ := s1
  obtain ⟨r2, d2⟩ := s2
  have r1' : (rk ρ (N ⊔ A) : ℝ) + rk ρ (N ⊓ A) = rk ρ N + rk ρ A := by exact_mod_cast r1
  have r2' : (rk ρ (A ⊔ B) : ℝ) + rk ρ (B ⊓ (N ⊔ A)) = rk ρ B + rk ρ (N ⊔ A) := by
    exact_mod_cast r2
  have key : θ * ((rk ρ (A ⊔ B) : ℝ) - rk ρ N) =
      θ * ((rk ρ B : ℝ) - rk ρ (B ⊓ (N ⊔ A))) + θ * ((rk ρ A : ℝ) - rk ρ (N ⊓ A)) := by
    rw [← mul_add]
    congr 1
    linarith
  rw [key]
  linarith
private theorem muMin_sup_le_muMin_of_orthogonal {R : Type u} {V : Type v} {E : Type w} [Ring R]
    [AddCommGroup V] [Module R V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (ρ : V →+ E)
    {A B : Submodule R V} (hA : IsLat ρ A) (hB : IsLat ρ B)
    (h : ∀ x ∈ A, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0) (hA0 : A ≠ ⊥) :
    muMin ρ (A ⊔ B) ≤ muMin ρ A := by
  have hM0 : A ⊔ B ≠ ⊥ := fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
  obtain ⟨hL, -, dAB⟩ := hnSum_orth ρ hA hB h
  have rAB := hnSum_orth_rk ρ h1 hA hB h
  rw [(h2 R V E ρ A hA hA0).2.1]
  intro N hN
  have hNB : ∀ x ∈ N, ∀ y ∈ B, inner ℝ (ρ x) (ρ y) = 0 := fun x hx y hy => h x (hN hx) y hy
  have hNl : IsLat ρ N := hnSum_isLat_mono ρ hA hN
  obtain ⟨-, -, dNB⟩ := hnSum_orth ρ hNl hB hNB
  have rNB := hnSum_orth_rk ρ h1 hNl hB hNB
  have key := ((h2 R V E ρ (A ⊔ B) hL hM0).2.1 (muMin ρ (A ⊔ B))).1 le_rfl (N ⊔ B)
    (sup_le_sup_right hN B)
  rw [rNB, rAB, dNB, dAB] at key
  push_cast at key
  have e : (rk ρ A : ℝ) - rk ρ N = ((rk ρ A : ℝ) + rk ρ B) - ((rk ρ N : ℝ) + rk ρ B) := by ring
  rw [e]
  linarith
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w x
namespace Formalism.HN
theorem _root_.solution (h1 : DegSupermod.{u, v, w}) (h2 : MuChar.{u, v, w}) (h3 : SatBasic.{u, v, w}) :
    HNSum.{u, v, w, x} := by
  classical
  intro R V E _ _ _ _ _ _ ρ
  refine ⟨?_, ?_⟩
  · intro L ι s A θ hL hs hA
    induction s using Finset.induction_on with
    | empty => exact absurd hs Finset.not_nonempty_empty
    | @insert a s ha ih =>
      rw [Finset.iSup_insert]
      have ha' := hA a (Finset.mem_insert_self a s)
      by_cases hs' : s.Nonempty
      · have hrest : ∀ i ∈ s, A i ≤ L ∧ A i ≠ ⊥ ∧ θ ≤ muMin ρ (A i) :=
          fun i hi => hA i (Finset.mem_insert_of_mem hi)
        have hle : (⨆ i ∈ s, A i) ≤ L := iSup₂_le fun i hi => (hrest i hi).1
        have hne : (⨆ i ∈ s, A i) ≠ ⊥ := by
          obtain ⟨j, hj⟩ := hs'
          intro hb
          apply (hrest j hj).2.1
          exact eq_bot_iff.2 ((le_iSup₂_of_le (f := fun i (_ : i ∈ s) => A i) j hj le_rfl).trans hb.le)
        exact le_muMin_sup_of_le_muMin h1 h2 ρ hL ha'.1 hle ha'.2.1 hne ha'.2.2 (ih hs' hrest)
      · rw [Finset.not_nonempty_iff_eq_empty.1 hs']
        simpa using ha'.2.2
  · intro A B hA hB h
    obtain ⟨hL, -, hdeg⟩ := hnSum_orth ρ hA hB h
    refine ⟨hL, hdeg, fun hA0 hB0 => ⟨?_, ?_⟩⟩
    · have hM0 : A ⊔ B ≠ ⊥ :=
        fun e => hA0 (eq_bot_iff.2 ((le_sup_left : A ≤ A ⊔ B).trans e.le))
      have mA := (h2 R V E ρ A hA hA0).1
      have mB := (h2 R V E ρ B hB hB0).1
      have mM := (h2 R V E ρ (A ⊔ B) hL hM0).1
      apply le_antisymm
      · rw [mM]
        intro N hN
        obtain ⟨hd, hr⟩ := hnSum_split ρ h1 hA hB h hN
        have eA := ((mA (muMax ρ A)).1 le_rfl) (N ⊓ A) inf_le_right
        have eB := ((mB (muMax ρ B)).1 le_rfl) (B ⊓ (N ⊔ A)) inf_le_left
        have fA : muMax ρ A * (rk ρ (N ⊓ A) : ℝ) ≤ max (muMax ρ A) (muMax ρ B) * rk ρ (N ⊓ A) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
        have fB : muMax ρ B * (rk ρ (B ⊓ (N ⊔ A)) : ℝ) ≤
            max (muMax ρ A) (muMax ρ B) * rk ρ (B ⊓ (N ⊔ A)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)
        rw [hr]
        push_cast
        linarith
      · apply max_le
        · rw [mA]
          intro N hN
          exact (mM _).1 le_rfl N (hN.trans le_sup_left)
        · rw [mB]
          intro N hN
          exact (mM _).1 le_rfl N (hN.trans le_sup_right)
    · apply le_antisymm
      · refine le_min (muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hA hB h hA0) ?_
        have h' : ∀ y ∈ B, ∀ x ∈ A, inner ℝ (ρ y) (ρ x) = 0 := by
          intro y hy x hx
          rw [real_inner_comm]
          exact h x hx y hy
        have := muMin_sup_le_muMin_of_orthogonal h1 h2 ρ hB hA h' hB0
        rwa [sup_comm] at this
      · exact le_muMin_sup_of_le_muMin h1 h2 ρ hL le_sup_left le_sup_right hA0 hB0
          (min_le_left _ _) (min_le_right _ _)
end Formalism.HN
