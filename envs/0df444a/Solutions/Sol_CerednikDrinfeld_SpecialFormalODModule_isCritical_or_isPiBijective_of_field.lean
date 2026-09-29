-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.isCritical_or_isPiBijective_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/815d0044-a087-59c9-96f3-dae099b42baa

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierNModule
import Definitions.Def_CerednikDrinfeld_CartierLMapFibre
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule FormalODModule.gradedPiece_add_two_mul FormalODModule.CritChart.IsCritical FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne"
namespace SpecialFormalODModule
p2m_export "CerednikDrinfeld.SpecialFormalODModule" "toFormalODModule isSpecial"
namespace FieldDichotomyProof
p2m_open "CerednikDrinfeld.SpecialFormalODModule CerednikDrinfeld"

p2m_open "MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field.CerednikDrinfeld CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [hp : Fact p.Prime]

section general

variable {B : Type u} [CommRing B] [CharP B p]

theorem piOp_verschiebung (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp (verschiebung f) = verschiebung (X.piOp f) :=
  map_verschiebung X.varpiEnd f

theorem piOp_piOp (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp (X.piOp f) = verschiebung (frobenius f) := by
  have h1 : X.piOp (X.piOp f) = CartierModule.endAct (X.varpiEnd * X.varpiEnd) f := by
    rw [map_mul]; rfl
  rw [h1, X.varpiEnd_mul_varpiEnd, map_natCast, endAct_natCast, verschiebung_frobenius]

theorem isCritical_succ_of_surjective (j : Zp2 p →+* B) (X : FormalODModule p B) (n : ℕ)
    (hs : ∀ h ∈ X.gradedPiece j (n + 1), ∃ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
      h = X.piOp f + verschiebung g) :
    CritChart.IsCritical X j (n + 1) := by
  intro h hh
  obtain ⟨f, -, g, rfl⟩ := hs h hh
  refine ⟨frobenius f + X.piOp g, ?_⟩
  show _ = X.piOp (X.piOp f + verschiebung g)
  rw [map_add, map_add, piOp_piOp, piOp_verschiebung]

end general

section lines

variable {k : Type u} [Field k] {E : Type u} [AddCommGroup E] [Module k E]

theorem exists_generator (U : Submodule k E) [Module.Invertible k U] :
    ∃ v ∈ U, v ≠ 0 ∧ ∀ w ∈ U, ∃ c : k, c • v = w := by
  have h1 : Module.finrank k U = 1 := Module.Invertible.finrank_eq_one k U
  obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.1 h1
  refine ⟨v, v.2, fun h => hv (Subtype.ext h), fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hgen ⟨w, hw⟩
  exact ⟨c, by simpa using congrArg Subtype.val hc⟩

theorem zero_or_bijOn (U W : Submodule k E) [Module.Invertible k U] [Module.Invertible k W]
    (T : E →ₗ[k] E) (hT : ∀ u ∈ U, T u ∈ W) :
    (∀ u ∈ U, T u = 0) ∨
      ((∀ u ∈ U, T u = 0 → u = 0) ∧ ∀ w ∈ W, ∃ u ∈ U, T u = w) := by
  obtain ⟨u₀, hu₀, hu₀0, hgenU⟩ := exists_generator U
  obtain ⟨w₀, hw₀, hw₀0, hgenW⟩ := exists_generator W
  by_cases h0 : T u₀ = 0
  · left
    intro u hu
    obtain ⟨c, rfl⟩ := hgenU u hu
    rw [map_smul, h0, smul_zero]
  · right
    constructor
    · intro u hu hTu
      obtain ⟨c, rfl⟩ := hgenU u hu
      rw [map_smul] at hTu
      rcases smul_eq_zero.1 hTu with hc | hc
      · rw [hc, zero_smul]
      · exact absurd hc h0
    ·
      obtain ⟨c₀, hc₀⟩ := hgenW (T u₀) (hT u₀ hu₀)
      have hc₀0 : c₀ ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc₀
        exact h0 hc₀.symm
      intro w hw
      obtain ⟨c, rfl⟩ := hgenW w hw
      refine ⟨(c * c₀⁻¹) • u₀, U.smul_mem _ hu₀, ?_⟩
      rw [map_smul, ← hc₀, smul_smul, mul_assoc, inv_mul_cancel₀ hc₀0, mul_one]

end lines

section field

variable {k : Type u} [Field k] [CharP k p]

def liePiece (j : Zp2 p →+* k) (X : FormalODModule p k) (n : ℕ) : Submodule k X.Lie :=
  if n % 2 = 0 then X.lieZero j else X.lieOne j

omit [CharP k p] in
theorem liePiece_zero (j : Zp2 p →+* k) (X : FormalODModule p k) : liePiece j X 0 = X.lieZero j := by
  simp [liePiece]

omit [CharP k p] in
theorem liePiece_one (j : Zp2 p →+* k) (X : FormalODModule p k) : liePiece j X 1 = X.lieOne j := by
  simp [liePiece]

omit [CharP k p] in
theorem liePiece_add_two (j : Zp2 p →+* k) (X : FormalODModule p k) (n : ℕ) :
    liePiece j X (n + 2) = liePiece j X n := by
  simp [liePiece]

omit [CharP k p] in
theorem liePiece_mod_two (j : Zp2 p →+* k) (X : FormalODModule p k) (n : ℕ) :
    liePiece j X (n % 2) = liePiece j X n := by
  simp [liePiece]

omit [CharP k p] in
theorem gradedPiece_mod_two (j : Zp2 p →+* k) (X : FormalODModule p k) (n : ℕ) :
    X.gradedPiece j (n % 2) = X.gradedPiece j n := by
  conv_rhs => rw [← Nat.mod_add_div n 2]
  exact (CerednikDrinfeld.FormalODModule.gradedPiece_add_two_mul X j (n % 2) (n / 2)).symm

structure Facts (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) : Prop where
  v_iff : ∀ (n : ℕ) (g : CartierModule p Φ.F),
    verschiebung g ∈ Φ.gradedPiece j (n + 1) ↔ g ∈ Φ.gradedPiece j n
  pi_mem : ∀ (n : ℕ), ∀ f ∈ Φ.gradedPiece j n, Φ.piOp f ∈ Φ.gradedPiece j (n + 1)
  tangent_surj : Function.Surjective (tangent : CartierModule p Φ.F → Fin 2 → k)
  tangent_eq_zero_iff : ∀ f : CartierModule p Φ.F, tangent f = 0 ↔ ∃ g, verschiebung g = f
  map_tangent : ∀ n : ℕ, (Φ.gradedPiece j n).map (tangent : CartierModule p Φ.F →+ Fin 2 → k) =
    (liePiece j Φ.toFormalODModule n).toAddSubgroup
  invertible : ∀ n : ℕ, Module.Invertible k (liePiece j Φ.toFormalODModule n)

theorem facts (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) : Facts j Φ := by
  obtain ⟨hLie, hinv0, hinv1⟩ := Φ.isSpecial
  obtain ⟨-, h2, -, h4, -, -, h7, h8⟩ :=
    CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j
      Φ.toFormalODModule hLie
  obtain ⟨hs, hk⟩ :=
    MvFormalGroup.CartierModule.tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq p Φ.F
  have hmap01 : ∀ r : ℕ, r < 2 → (Φ.gradedPiece j r).map (tangent : CartierModule p Φ.F →+ Fin 2 → k) =
      (liePiece j Φ.toFormalODModule r).toAddSubgroup := by
    intro r hr
    interval_cases r
    · rw [liePiece_zero]; exact h7
    · rw [liePiece_one]; exact h8
  have hinv01 : ∀ r : ℕ, r < 2 → Module.Invertible k (liePiece j Φ.toFormalODModule r) := by
    intro r hr
    interval_cases r
    · rw [liePiece_zero]; exact hinv0
    · rw [liePiece_one]; exact hinv1
  refine ⟨h2, fun n f hf => h4 n f hf, hs, hk, fun n => ?_, fun n => ?_⟩
  · rw [← gradedPiece_mod_two, ← liePiece_mod_two]
    exact hmap01 (n % 2) (Nat.mod_lt n two_pos)
  · rw [← liePiece_mod_two]
    exact hinv01 (n % 2) (Nat.mod_lt n two_pos)

def piLie (X : FormalODModule p k) : X.Lie →ₗ[k] X.Lie :=
  Matrix.mulVecLin (MvFormalGroup.linearPart X.varpi)

omit [CharP k p] in
theorem tangent_piOp (X : FormalODModule p k) (f : CartierModule p X.F) :
    tangent (X.piOp f) = piLie X (tangent f) :=
  tangent_map X.varpiEnd f

theorem mem_liePiece_iff (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) (hF : Facts j Φ) (n : ℕ)
    (v : Fin 2 → k) :
    v ∈ liePiece j Φ.toFormalODModule n ↔ ∃ f ∈ Φ.gradedPiece j n, tangent f = v := by
  have h := hF.map_tangent n
  constructor
  · intro hv
    have hv' : v ∈ (liePiece j Φ.toFormalODModule n).toAddSubgroup := hv
    rw [← h] at hv'
    obtain ⟨f, hf, hfv⟩ := AddSubgroup.mem_map.1 hv'
    exact ⟨f, hf, hfv⟩
  · rintro ⟨f, hf, rfl⟩
    have : tangent f ∈ (Φ.gradedPiece j n).map (tangent : CartierModule p Φ.F →+ Fin 2 → k) :=
      AddSubgroup.mem_map.2 ⟨f, hf, rfl⟩
    rw [h] at this
    exact this

theorem piLie_mem (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) (hF : Facts j Φ) (n : ℕ) :
    ∀ u ∈ liePiece j Φ.toFormalODModule n,
      piLie Φ.toFormalODModule u ∈ liePiece j Φ.toFormalODModule (n + 1) := by
  intro u hu
  obtain ⟨f, hf, rfl⟩ := (mem_liePiece_iff j Φ hF n u).1 hu
  rw [← tangent_piOp]
  exact (mem_liePiece_iff j Φ hF (n + 1) _).2 ⟨_, hF.pi_mem n f hf, rfl⟩

theorem isCritical_of_zero (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) (hF : Facts j Φ) (n : ℕ)
    (h0 : ∀ u ∈ liePiece j Φ.toFormalODModule n, piLie Φ.toFormalODModule u = 0) :
    CritChart.IsCritical Φ.toFormalODModule j n := by
  intro f hf
  have ht : tangent (Φ.piOp f) = 0 := by
    rw [tangent_piOp]
    exact h0 _ ((mem_liePiece_iff j Φ hF n _).2 ⟨f, hf, rfl⟩)
  obtain ⟨g, hg⟩ := (hF.tangent_eq_zero_iff _).1 ht
  exact ⟨g, hg⟩

theorem isPiBijective_of_bijOn (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) (hF : Facts j Φ)
    (n : ℕ)
    (hinj : ∀ u ∈ liePiece j Φ.toFormalODModule n, piLie Φ.toFormalODModule u = 0 → u = 0)
    (hsurj : ∀ w ∈ liePiece j Φ.toFormalODModule (n + 1),
      ∃ u ∈ liePiece j Φ.toFormalODModule n, piLie Φ.toFormalODModule u = w) :
    Φ.IsPiBijective j n := by
  constructor
  · rintro f hf ⟨g, hg⟩
    have ht : tangent f = 0 := by
      apply hinj _ ((mem_liePiece_iff j Φ hF n _).2 ⟨f, hf, rfl⟩)
      rw [← tangent_piOp, ← hg, tangent_verschiebung]
    obtain ⟨g', hg'⟩ := (hF.tangent_eq_zero_iff _).1 ht
    exact ⟨g', hg'⟩
  · intro h hh
    obtain ⟨u, hu, hu'⟩ := hsurj _ ((mem_liePiece_iff j Φ hF (n + 1) _).2 ⟨h, hh, rfl⟩)
    obtain ⟨f, hf, rfl⟩ := (mem_liePiece_iff j Φ hF n u).1 hu
    have ht : tangent (h - Φ.piOp f) = 0 := by
      rw [map_sub, tangent_piOp, hu', sub_self]
    obtain ⟨g, hg⟩ := (hF.tangent_eq_zero_iff _).1 ht
    exact ⟨f, hf, g, by rw [hg, add_sub_cancel]⟩

theorem isCritical_or_isPiBijective (j : Zp2 p →+* k) (Φ : SpecialFormalODModule p j) (hF : Facts j Φ)
    (n : ℕ) : CritChart.IsCritical Φ.toFormalODModule j n ∨ Φ.IsPiBijective j n := by
  haveI := hF.invertible n
  haveI := hF.invertible (n + 1)
  rcases zero_or_bijOn (liePiece j Φ.toFormalODModule n) (liePiece j Φ.toFormalODModule (n + 1))
      (piLie Φ.toFormalODModule) (piLie_mem j Φ hF n) with h0 | ⟨hinj, hsurj⟩
  · exact Or.inl (isCritical_of_zero j Φ hF n h0)
  · exact Or.inr (isPiBijective_of_bijOn j Φ hF n hinj hsurj)

end field

end CerednikDrinfeld.SpecialFormalODModule.FieldDichotomyProof

end

open CerednikDrinfeld.SpecialFormalODModule.FieldDichotomyProof in
theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    (∀ n : ℕ, CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j n ∨
        Φ.IsPiBijective j n) ∧
      (CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 0 ∨
        CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j 1) := by
  have hF := facts j Φ
  refine ⟨fun n => isCritical_or_isPiBijective j Φ hF n, ?_⟩
  rcases isCritical_or_isPiBijective j Φ hF 0 with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (isCritical_succ_of_surjective j Φ.toFormalODModule 0 h0.2)

end S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_isCritical_or_isPiBijective_of_field (solution)
