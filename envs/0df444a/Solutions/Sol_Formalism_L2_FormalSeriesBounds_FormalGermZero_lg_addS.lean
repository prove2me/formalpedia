-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FormalGermZero.lg_addS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:40.748346+00:00
-- url     : https://prove2.me/submissions/00720d41-2621-465d-b254-339e080f22ce

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_pair_const
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
namespace FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
private theorem cc_subst_lemma {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]
section Law
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
private theorem prod_X_lemma {σ τ A : Type} [CommRing A] (e : σ → τ) (d : σ →₀ ℕ) :
    (d.prod fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) =
      MvPowerSeries.monomial (d.mapDomain e) 1 := by
  classical
  refine Finsupp.induction d ?_ ?_
  · simp only [Finsupp.prod_zero_index, Finsupp.mapDomain_zero]
    rfl
  · intro a b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun s n => (MvPowerSeries.X (e s) : MvPowerSeries τ A) ^ n) (pow_zero _), ih, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial, mul_one]
private theorem un1_lift_lemma_2 (f : MvPowerSeries (Fin 1 × Fin dd) C) :
    MvPowerSeries.subst (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C))
      (un1 f) = f := by
  classical
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))]
  simp only [prod_X_lemma (Prod.mk (0 : Fin 1)), MvPowerSeries.coeff_monomial]
  have hμ : (μ.mapDomain Prod.snd).mapDomain (Prod.mk (0 : Fin 1)) = μ := by
    rw [← Finsupp.mapDomain_comp]
    have hc : (Prod.mk (0 : Fin 1) ∘ (Prod.snd : Fin 1 × Fin dd → Fin dd)) = id := by
      funext p
      exact Prod.ext (Subsingleton.elim _ _) rfl
    rw [hc, Finsupp.mapDomain_id]
  rw [finsum_eq_single _ (μ.mapDomain Prod.snd)]
  · rw [if_pos hμ.symm, smul_eq_mul, mul_one]
    show MvPowerSeries.coeff ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 1), x))) f = _
    rw [show (fun x : Fin dd => ((0 : Fin 1), x)) = Prod.mk (0 : Fin 1) from rfl, hμ]
  · intro d hd
    rw [if_neg, smul_zero]
    intro h
    apply hd
    rw [h, ← Finsupp.mapDomain_comp,
      show (Prod.snd ∘ Prod.mk (0 : Fin 1) : Fin dd → Fin dd) = id from rfl, Finsupp.mapDomain_id]
private theorem ev1_lemma_3 {n : ℕ} (Q : Pt C n dd) (hQ : ∀ i, MvPowerSeries.constantCoeff (Q i) = 0)
    (f : PS C 1 dd) : ev ![Q] f = MvPowerSeries.subst Q (un1 f) := by
  have hA : MvPowerSeries.HasSubst
      (fun i : Fin dd => (MvPowerSeries.X ((0 : Fin 1), i) : MvPowerSeries (Fin 1 × Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hB : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin dd => (![Q] : Fin 1 → Pt C n dd) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨a, i⟩
      fin_cases a
      exact hQ i)
  unfold ev
  conv_lhs => rw [← un1_lift_lemma_2 f]
  rw [MvPowerSeries.subst_comp_subst_apply hA hB]
  congr 1
  funext i
  rw [MvPowerSeries.subst_X hB]
  rfl
end Law
section Sys1
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)]
end Sys1
end FormalGermZero
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
namespace Formalism.L2.FormalSeriesBounds.FormalGermZero
theorem _root_.solution {σ : Type} (Y : FBChart C V O dd) (a b : Fin dd → MvPowerSeries σ C)
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) (hb : ∀ j, MvPowerSeries.constantCoeff (b j) = 0)
    (i : Fin dd) :
    MvPowerSeries.subst (addS Y.B.G.F a b) (un1 (Y.lg i)) =
      MvPowerSeries.subst a (un1 (Y.lg i)) + MvPowerSeries.subst b (un1 (Y.lg i)) := by
  have hpt : ∀ k : Fin 2, ∀ i, MvPowerSeries.constantCoeff (pt C dd k i) = 0 := fun k i => by simp [pt]
  have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C dd 0) (pt C dd 1) i) = 0 := fun i => by
    show MvPowerSeries.constantCoeff (ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i)) = 0
    unfold ev
    rw [cc_subst_lemma _ (fun p => by
      rcases p with ⟨a, k⟩
      fin_cases a <;> simp [pt])]
    exact Y.B.G.const i
  have hF' : addOf Y.B.G.F (pt C dd 0) (pt C dd 1) = Y.B.G.F := by
    funext i
    show ev (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) (Y.B.G.F i) = Y.B.G.F i
    have hX : (fun p : Fin 2 × Fin dd => (![pt C dd 0, pt C dd 1] : Fin 2 → Pt C 2 dd) p.1 p.2) =
        MvPowerSeries.X := by
      funext p
      rcases p with ⟨a, k⟩
      fin_cases a <;> rfl
    unfold ev
    rw [hX, ← MvPowerSeries.map_algebraMap_eq_subst_X]
    simp
  have hfb := Y.lg_add i
  rw [ev1_lemma_3 _ hadd, ev1_lemma_3 _ (hpt 0), ev1_lemma_3 _ (hpt 1), hF'] at hfb
  have hP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (pair_const ha hb)
  have hF : MvPowerSeries.HasSubst Y.B.G.F := MvPowerSeries.hasSubst_of_constantCoeff_zero Y.B.G.const
  have hX0 : MvPowerSeries.HasSubst (pt C dd (0 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 0)
  have hX1 : MvPowerSeries.HasSubst (pt C dd (1 : Fin 2)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (hpt 1)
  have e := congrArg (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => ![a, b] q.1 q.2)) hfb
  rw [MvPowerSeries.subst_comp_subst_apply hF hP, MvPowerSeries.subst_add hP,
    MvPowerSeries.subst_comp_subst_apply hX0 hP, MvPowerSeries.subst_comp_subst_apply hX1 hP] at e
  simp only [pt, MvPowerSeries.subst_X hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at e
  exact e
end Formalism.L2.FormalSeriesBounds.FormalGermZero
