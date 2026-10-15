-- Prove2me | solution 1 for GaugeFunctor.aharonov_bohm_nonabelian
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-14T17:54:02.100996+00:00
-- url     : https://prove2.me/submissions/ff461a8b-f417-4f4c-a991-5039d9ec1b47

import Mathlib
import Definitions.Def_GaugeFunctor_defs
import Theorems.Thm_GaugeFunctor_not_faithful_of_toDiscrete

open CategoryTheory

namespace GaugeFunctor

theorem abn_circle_not_full (G : Type) [Group G] [Nontrivial G] :
    ¬ (curvF G circleC).Full := by
  intro hF
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  let A : PotG circleC.toGraph G := ⟨fun _ => 1⟩
  let B : PotG circleC.toGraph G := ⟨fun e => if e.1 = 0 then a else 1⟩
  have hobj : (curvF G circleC).obj A = (curvF G circleC).obj B := by
    apply Discrete.ext; funext f; exact f.elim0
  obtain ⟨g, -⟩ := hF.map_surjective (eqToHom hobj)
  have h0 := congrFun g.2 (0 : Fin 3)
  have h1 := congrFun g.2 (1 : Fin 3)
  have h2 := congrFun g.2 (2 : Fin 3)
  simp [gaugeAct, A, B, circleC] at h0 h1 h2
  rw [mul_inv_eq_one] at h1 h2
  rw [h1, h2, mul_inv_cancel] at h0
  exact ha h0.symm

theorem abn_filled_hol {G : Type} [Group G] (A : Fin filledC.toGraph.nE → G)
    (f : Fin filledC.nF) :
    hol filledC.toGraph G A (filledC.bd f) = A (0 : Fin 3) * A (1 : Fin 3) * A (2 : Fin 3) := by
  simp [hol, stepHol, filledC, mul_assoc]

theorem abn_filled_full (G : Type) [Group G] : (curvF G filledC).Full := by
  refine ⟨fun {A B} f => ?_⟩
  have h := congrFun (Discrete.eq_of_hom f) (⟨0, by decide⟩ : Fin filledC.nF)
  simp only [curvF] at h
  simp only [abn_filled_hol] at h
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff] at h
  obtain ⟨c, hc⟩ := h
  let g : Fin 3 → G := ![c, (B.conn (0 : Fin 3))⁻¹ * c * A.conn (0 : Fin 3),
    (B.conn (1 : Fin 3))⁻¹ * (B.conn (0 : Fin 3))⁻¹ * c * A.conn (0 : Fin 3) * A.conn (1 : Fin 3)]
  have hg : gaugeAct filledC.toGraph G g A.conn = B.conn := by
    funext e
    fin_cases e
    · simp [gaugeAct, g, filledC]
    · simp [gaugeAct, g, filledC]
    · show g 2 * A.conn (2 : Fin 3) * (g 0)⁻¹ = B.conn (2 : Fin 3)
      calc g 2 * A.conn (2 : Fin 3) * (g 0)⁻¹
          = (B.conn (1 : Fin 3))⁻¹ * (B.conn (0 : Fin 3))⁻¹ *
              (c * (A.conn (0 : Fin 3) * A.conn (1 : Fin 3) * A.conn (2 : Fin 3)) * c⁻¹) := by
            simp only [g, Matrix.cons_val]; group
        _ = B.conn (2 : Fin 3) := by rw [hc]; group
  exact ⟨⟨g, hg⟩, Subsingleton.elim _ _⟩

theorem abn_filled_essSurj (G : Type) [Group G] : (curvF G filledC).EssSurj := by
  refine ⟨fun Y => ?_⟩
  obtain ⟨φ⟩ := Y
  obtain ⟨r, hr⟩ := ConjClasses.mk_surjective (φ ⟨0, by decide⟩)
  let A : PotG filledC.toGraph G := ⟨fun e => if e.1 = 0 then r else 1⟩
  refine ⟨A, ⟨eqToIso ?_⟩⟩
  apply Discrete.ext
  funext f
  show ConjClasses.mk (hol filledC.toGraph G A.conn (filledC.bd f)) = φ f
  have hf : f = ⟨0, by decide⟩ := Fin.ext (by have h : f.1 < 1 := f.2; show f.1 = 0; omega)
  rw [abn_filled_hol, hf, ← hr]
  simp [A]

theorem abn_main (G : Type) [Group G] [Nontrivial G] :
    ¬ (curvF G circleC).Full ∧
      (curvF G filledC).Full ∧ (curvF G filledC).EssSurj ∧ ¬ (curvF G filledC).Faithful :=
  ⟨abn_circle_not_full G, abn_filled_full G, abn_filled_essSurj G,
    not_faithful_of_toDiscrete filledC.toGraph G ⟨(0 : Fin 3)⟩ (curvF G filledC)⟩

end GaugeFunctor

open GaugeFunctor CategoryTheory in
theorem solution (G : Type) [Group G] [Nontrivial G] :
    ¬ (curvF G circleC).Full ∧
      (curvF G filledC).Full ∧ (curvF G filledC).EssSurj ∧ ¬ (curvF G filledC).Faithful :=
  abn_main G
