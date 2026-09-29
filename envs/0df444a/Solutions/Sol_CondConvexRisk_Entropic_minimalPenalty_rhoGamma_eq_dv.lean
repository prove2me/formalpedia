-- Prove2me | solution 1 for CondConvexRisk.Entropic.minimalPenalty_rhoGamma_eq_dv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:50:53.707518+00:00
-- url     : https://prove2.me/submissions/70fe9cdb-6819-419b-9c37-7729462202c4

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic
import Definitions.Def_CondConvexRisk_Entropic_EntropicRisk

open MeasureTheory

namespace CondConvexRisk.Entropic

lemma aux_mpdv_cancel (a b : ℝ) (h : a * b = 1) (x : EReal) :
    (a : EReal) * ((b : EReal) * x) = x := by
  rw [← mul_assoc, ← EReal.coe_mul, h, EReal.coe_one, one_mul]

lemma aux_mpdv_dir {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ι → Ω → EReal) (G : κ → Ω → EReal) (c : ℝ) (hc : 0 < c)
    (h1 : ∀ i, ∃ k, G k =ᵐ[P] fun ω => (c : EReal) * F i ω)
    (h2 : ∀ k, ∃ i, G k =ᵐ[P] fun ω => (c : EReal) * F i ω) (V : Ω → EReal) :
    IsEssSup P F V → IsEssSup P G (fun ω => (c : EReal) * V ω) := by
  rintro ⟨hV, hle, hmin⟩
  have hc0 : (0 : EReal) ≤ (c : EReal) := EReal.coe_nonneg.2 hc.le
  have hci0 : (0 : EReal) ≤ ((c⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.2 (inv_pos.2 hc).le
  refine ⟨hV.const_mul _, ?_, ?_⟩
  · intro k
    obtain ⟨i, hi⟩ := h2 k
    filter_upwards [hi, hle i] with ω h1 h2
    rw [h1]
    exact mul_le_mul_of_nonneg_left h2 hc0
  · intro W hW hWle
    have key : V ≤ᵐ[P] fun ω => ((c⁻¹ : ℝ) : EReal) * W ω := by
      refine hmin _ (hW.const_mul _) (fun i => ?_)
      obtain ⟨k, hk⟩ := h1 i
      filter_upwards [hk, hWle k] with ω h1 h2
      rw [h1] at h2
      calc F i ω = ((c⁻¹ : ℝ) : EReal) * ((c : EReal) * F i ω) :=
            (aux_mpdv_cancel _ _ (inv_mul_cancel₀ hc.ne') _).symm
        _ ≤ ((c⁻¹ : ℝ) : EReal) * W ω := mul_le_mul_of_nonneg_left h2 hci0
    filter_upwards [key] with ω h
    calc (c : EReal) * V ω ≤ (c : EReal) * (((c⁻¹ : ℝ) : EReal) * W ω) :=
          mul_le_mul_of_nonneg_left h hc0
      _ = W ω := aux_mpdv_cancel _ _ (mul_inv_cancel₀ hc.ne') _

lemma aux_mpdv_QP {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (Q : PG m P) {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (h : f =ᵐ[Q.1] g) : f =ᵐ[P] g := by
  have hs : MeasurableSet[m] {ω | f ω = g ω} := hf.measurableSet_eq_fun hg
  have hs' : MeasurableSet[m] {ω | ¬ f ω = g ω} := hs.compl
  rw [Filter.EventuallyEq, ae_iff] at h ⊢
  rw [← Q.2.2.2 _ hs']
  exact h

lemma aux_mpdv_core {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} (γ : ℝ) (hγ : γ ≠ 0) (Q : PG m P)
    (X Z : LInf P) (hZ : Z.1 = fun x => -γ * X.1 x) :
    (dvFamily m P Q Z =ᵐ[P]
        fun ω => (γ : EReal) * penaltyFamily m P (rhoGamma m P γ) Q X ω) ∧
      (penaltyFamily m P (rhoGamma m P γ) Q X =ᵐ[P]
        fun ω => ((γ⁻¹ : ℝ) : EReal) * dvFamily m P Q Z ω) := by
  have hce : Q.1[Z.1 | m] =ᵐ[P] fun ω => -γ * Q.1[X.1 | m] ω := by
    apply aux_mpdv_QP Q stronglyMeasurable_condExp
      (stronglyMeasurable_condExp.const_mul (-γ))
    rw [hZ]
    exact condExp_smul (-γ) X.1 m
  have hexp : (fun x => Real.exp (Z.1 x)) = fun x => Real.exp (-γ * X.1 x) := by
    rw [hZ]
  constructor
  · filter_upwards [hce] with ω hω
    simp only [dvFamily, penaltyFamily, rhoGamma]
    rw [hexp, hω, ← EReal.coe_mul]
    congr 1
    field_simp
  · filter_upwards [hce] with ω hω
    simp only [dvFamily, penaltyFamily, rhoGamma]
    rw [hexp, hω, ← EReal.coe_mul]
    congr 1
    field_simp

end CondConvexRisk.Entropic

open MeasureTheory CondConvexRisk.Entropic

theorem solution {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    (γ : ℝ) (hγ : 0 < γ) (Q : PG m P) (V : Ω → EReal) :
    IsEssSup P (dvFamily m P Q) V ↔
      IsEssSup P (penaltyFamily m P (rhoGamma m P γ) Q) (fun ω => ((γ⁻¹ : ℝ) : EReal) * V ω) := by
  have hγ0 : γ ≠ 0 := hγ.ne'
  -- Z = -γ X
  have hA : ∀ X : LInf P, ∃ Z : LInf P, Z.1 = fun x => -γ * X.1 x :=
    fun X => ⟨⟨fun x => -γ * X.1 x, X.2.const_mul _⟩, rfl⟩
  -- X = -γ⁻¹ Z
  have hB : ∀ Z : LInf P, ∃ X : LInf P, Z.1 = fun x => -γ * X.1 x := by
    intro Z
    refine ⟨⟨fun x => -γ⁻¹ * Z.1 x, Z.2.const_mul _⟩, ?_⟩
    funext x
    simp only
    field_simp
  constructor
  · apply aux_mpdv_dir _ _ γ⁻¹ (inv_pos.2 hγ)
    · intro Z
      obtain ⟨X, hX⟩ := hB Z
      exact ⟨X, (aux_mpdv_core γ hγ0 Q X Z hX).2⟩
    · intro X
      obtain ⟨Z, hZ⟩ := hA X
      exact ⟨Z, (aux_mpdv_core γ hγ0 Q X Z hZ).2⟩
  · intro h
    have := aux_mpdv_dir (P := P) (penaltyFamily m P (rhoGamma m P γ) Q) (dvFamily m P Q) γ hγ
      (fun X => by
        obtain ⟨Z, hZ⟩ := hA X
        exact ⟨Z, (aux_mpdv_core γ hγ0 Q X Z hZ).1⟩)
      (fun Z => by
        obtain ⟨X, hX⟩ := hB Z
        exact ⟨X, (aux_mpdv_core γ hγ0 Q X Z hX).1⟩) _ h
    convert this using 1
    funext ω
    exact (aux_mpdv_cancel _ _ (mul_inv_cancel₀ hγ0) _).symm
