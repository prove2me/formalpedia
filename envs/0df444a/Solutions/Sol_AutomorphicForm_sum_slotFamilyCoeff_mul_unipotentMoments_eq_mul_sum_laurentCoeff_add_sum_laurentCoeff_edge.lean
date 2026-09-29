-- Prove2me | solution 1 for AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/73630c90-7cd3-5bf4-91d0-d1312b5d1e23

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero
import Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace ArrayAlgGlue

theorem sum_pi_prod_attach_mul_prod {ι β : Type*} [DecidableEq ι] (T : Finset ι) (t : ι → Finset β)
    (c : ι → β → ℂ) (F : T → β → ℂ) :
    ∑ m ∈ T.pi t, (∏ v ∈ T.attach, c v.1 (m v.1 v.2)) * ∏ i : T, F i (m i.1 i.2) =
      ∏ i : T, ∑ r ∈ t i.1, c i.1 r * F i r := by
  classical
  have key := Finset.prod_sum (s := T) (t := t) (f := fun v r => c v r * (if h : v ∈ T then F ⟨v, h⟩ r else 0))

  have lhs : (∏ a ∈ T, ∑ b ∈ t a, c a b * (if h : a ∈ T then F ⟨a, h⟩ b else 0)) =
      ∏ i : T, ∑ r ∈ t i.1, c i.1 r * F i r := by
    rw [← Finset.prod_attach T (fun a => ∑ b ∈ t a, c a b * (if h : a ∈ T then F ⟨a, h⟩ b else 0)),
      Finset.univ_eq_attach]
    refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
    rw [dif_pos i.2]
  have rhs : (∑ p ∈ T.pi t, ∏ x ∈ T.attach, c x.1 (p x.1 x.2) * (if h : x.1 ∈ T then F ⟨x.1, h⟩ (p x.1 x.2) else 0)) =
      ∑ m ∈ T.pi t, (∏ v ∈ T.attach, c v.1 (m v.1 v.2)) * ∏ i : T, F i (m i.1 i.2) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.prod_mul_distrib, Finset.univ_eq_attach]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dif_pos i.2]
  rw [← lhs, key, rhs]

theorem sum_pi_prod_attach_mul_sum_mul_prod_erase {ι β : Type*} [DecidableEq ι] (T : Finset ι) (t : ι → Finset β)
    (c : ι → β → ℂ) (F H : T → β → ℂ) :
    ∑ m ∈ T.pi t, (∏ v ∈ T.attach, c v.1 (m v.1 v.2)) *
        ∑ p : T, H p (m p.1 p.2) * ∏ i ∈ Finset.univ.erase p, F i (m i.1 i.2) =
      ∑ p : T, (∑ r ∈ t p.1, c p.1 r * H p r) * ∏ i ∈ Finset.univ.erase p, ∑ r ∈ t i.1, c i.1 r * F i r := by
  classical

  have step : ∀ m ∈ T.pi t, (∏ v ∈ T.attach, c v.1 (m v.1 v.2)) *
        ∑ p : T, H p (m p.1 p.2) * ∏ i ∈ Finset.univ.erase p, F i (m i.1 i.2) =
      ∑ p : T, (∏ v ∈ T.attach, c v.1 (m v.1 v.2)) *
        ∏ i : T, (if i = p then H i else F i) (m i.1 i.2) := by
    intro m _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase (Finset.univ : Finset T) (fun i : T => (if i = p then H i else F i) (m i.1 i.2)) (Finset.mem_univ p)]
    rw [if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_pi_prod_attach_mul_prod T t c (fun i => if i = p then H i else F i)]
  rw [← Finset.mul_prod_erase (Finset.univ : Finset T) (fun i : T => ∑ r ∈ t i.1, c i.1 r * (if i = p then H i else F i) r)
    (Finset.mem_univ p)]
  rw [if_pos rfl]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [if_neg (Finset.ne_of_mem_erase hi)]

theorem sum_piFinset_prod_mul_prod_ite_eq_zero {N : ℕ} (B : Fin N → Finset ℤ) (hB : ∀ i, (0 : ℤ) ∈ B i)
    (g : Fin N → ℤ → ℂ) :
    ∑ n ∈ Fintype.piFinset B, (∏ i, g i (n i)) * ∏ i, (if n i = 0 then (1 : ℂ) else 0) = ∏ i, g i 0 := by
  classical
  have : ∀ n ∈ Fintype.piFinset B, (∏ i, g i (n i)) * ∏ i, (if n i = 0 then (1 : ℂ) else 0) =
      ∏ i, (g i (n i) * if n i = 0 then (1 : ℂ) else 0) := fun n _ => (Finset.prod_mul_distrib).symm
  rw [Finset.sum_congr rfl this]
  refine Eq.trans (Finset.prod_univ_sum B (fun i j => g i j * (if j = 0 then (1 : ℂ) else 0))).symm ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem (0 : ℤ) (hB i)]
  · simp
  · intro b _ hb; simp [hb]

theorem sum_piFinset_prod_mul_prod_erase_ite_mul {N : ℕ} (B : Fin N → Finset ℤ) (hB : ∀ i, (0 : ℤ) ∈ B i)
    (g : Fin N → ℤ → ℂ) (p : Fin N) (e : ℤ → ℂ) :
    ∑ n ∈ Fintype.piFinset B, (∏ i, g i (n i)) * ((∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0)) * e (n p)) =
      (∑ r ∈ B p, g p r * e r) * ∏ i ∈ Finset.univ.erase p, g i 0 := by
  classical
  have : ∀ n ∈ Fintype.piFinset B,
      (∏ i, g i (n i)) * ((∏ i ∈ Finset.univ.erase p, (if n i = 0 then (1 : ℂ) else 0)) * e (n p)) =
      ∏ i, (g i (n i) * if i = p then e (n i) else (if n i = 0 then (1 : ℂ) else 0)) := by
    intro n _
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
      (fun i => if i = p then e (n i) else (if n i = 0 then (1 : ℂ) else 0)) (Finset.mem_univ p)]
    rw [if_pos rfl, mul_comm (e (n p))]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  rw [Finset.sum_congr rfl this]
  refine Eq.trans (Finset.prod_univ_sum B (fun i j => g i j * (if i = p then e j else if j = 0 then (1 : ℂ) else 0))).symm ?_
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
    (fun i => ∑ j ∈ B i, g i j * (if i = p then e j else if j = 0 then (1 : ℂ) else 0)) (Finset.mem_univ p)]
  simp only [if_true]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [if_neg (Finset.ne_of_mem_erase hi)]
  rw [Finset.sum_eq_single_of_mem (0 : ℤ) (hB i)]
  · simp
  · intro b _ hb; simp [hb]

end ArrayAlgGlue

open NumberField NumberField.AdelicLevel IsDedekindDomain

open AutomorphicForm NumberField.AdelicLevel in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (σr s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hσ : ∀ v ∈ T, σr v ^ 2 = HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hs : ∀ v ∈ T, ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ) * s v) =
      σr v ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ∀ v ∈ T,
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hNws : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal =
      Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (Λ κ₀ : ℂ) (c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ) (R : ℝ) :
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      SatakeCombination.slotFamilyCoeff K L ws ks js T m *
        (Λ * ((R : ℂ) *
                ∏ i : T,
                  ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                    ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1) +
                ∑ p : T,
                  (c₁ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1) +
                      c₂ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m p.1 p.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1)) *
                    ∏ i ∈ Finset.univ.erase p,
                      ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) +
              κ₀ * ∏ i : T,
                ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                  ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) =
      (R : ℂ) * (Λ *
          ∑ n ∈ Fintype.piFinset
            (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
          (∏ i : Fin T.card,
            ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
              LaurentPolynomial ℂ).coeff (n i)) *
          (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
        (Λ * ∑ p : T,
            (c₁ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              ((∏ i ∈ Finset.univ.erase (T.equivFin p), (if n i = 0 then (1 : ℂ) else 0)) *
                (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * (n (T.equivFin p)).natAbs))) +
             c₂ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
          κ₀ *
            ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                  s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                LaurentPolynomial ℂ).coeff (n i)) *
            (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) := by
  classical

  set A : HeightOneSpectrum (𝓞 K) → (Fin 2 →₀ ℕ) → ℂ := fun v r =>
    (1 + (-1 : ℂ) ^ r 0) / 2 * (4 * (HeckeEigensystem.cNorm v * ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (r 0 / 2) *
      ((∏ n ∈ Finset.range (r 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ r 1 with hA
  set B : HeightOneSpectrum (𝓞 K) → (Fin 2 →₀ ℕ) → ℂ := fun v r =>
    (1 + (-1 : ℂ) ^ r 0) * (4 * (HeckeEigensystem.cNorm v * ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (r 0 / 2) *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ r 1 with hB
  set G0 : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ) * s v) ^ ks v * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js v *
      ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks v : LaurentPolynomial ℂ).coeff 0 with hG0
  set GE : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ) * s v) ^ ks v * ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js v *
      ∑ n ∈ Finset.Icc (-(ks v : ℤ)) (ks v),
        ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks v : LaurentPolynomial ℂ).coeff n *
          (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws v * n.natAbs)) with hGE
  set g : Fin T.card → ℤ → ℂ := fun i n =>
    ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) * s (T.equivFin.symm i).1) ^
        ks (T.equivFin.symm i).1 *
      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
      ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 : LaurentPolynomial ℂ).coeff n with hg

  have hP1 : ∀ v : T, ∑ r ∈ (SatakeCombination.slotWord K L ws v.1 (ks v.1) (js v.1)).support,
      SatakeCombination.slotCoeff K L ws v.1 (ks v.1) (js v.1) r * A v.1 r = G0 v.1 := fun v =>
    AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero K L ws v.1 (w' v.1) _ _ (σr v.1) (s v.1) (hσ v.1 v.2) (hs v.1 v.2) (hζ v.1 v.2) (hNws v.1 v.2) (ks v.1) (js v.1)
  have hP2 : ∀ v : T, ∑ r ∈ (SatakeCombination.slotWord K L ws v.1 (ks v.1) (js v.1)).support,
      SatakeCombination.slotCoeff K L ws v.1 (ks v.1) (js v.1) r * B v.1 r = GE v.1 := fun v =>
    AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge K L ws v.1 (w' v.1) _ _ (σr v.1) (s v.1) (hσ v.1 v.2) (hs v.1 v.2) (hζ v.1 v.2) (hNws v.1 v.2) (ks v.1) (js v.1)

  have e1 : ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
      ∏ i : T, A i.1 (m i.1 i.2) = ∏ i : T, G0 i.1 := by
    have := ArrayAlgGlue.sum_pi_prod_attach_mul_prod T (fun v => (SatakeCombination.slotWord K L ws v (ks v) (js v)).support)
      (fun v r => SatakeCombination.slotCoeff K L ws v (ks v) (js v) r) (fun i r => A i.1 r)
    refine Eq.trans this (Finset.prod_congr rfl fun i _ => hP1 i)
  have e2 : ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T, SatakeCombination.slotFamilyCoeff K L ws ks js T m *
      ∑ p : T, (c₁ p.1 * B p.1 (m p.1 p.2) + c₂ p.1 * A p.1 (m p.1 p.2)) * ∏ i ∈ Finset.univ.erase p, A i.1 (m i.1 i.2) =
      ∑ p : T, (c₁ p.1 * GE p.1 + c₂ p.1 * G0 p.1) * ∏ i ∈ Finset.univ.erase p, G0 i.1 := by
    have := ArrayAlgGlue.sum_pi_prod_attach_mul_sum_mul_prod_erase T
      (fun v => (SatakeCombination.slotWord K L ws v (ks v) (js v)).support)
      (fun v r => SatakeCombination.slotCoeff K L ws v (ks v) (js v) r) (fun i r => A i.1 r)
      (fun p r => c₁ p.1 * B p.1 r + c₂ p.1 * A p.1 r)
    refine Eq.trans this (Finset.sum_congr rfl fun p _ => ?_)
    congr 1
    · rw [← hP1 p, ← hP2 p, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    · exact Finset.prod_congr rfl fun i _ => hP1 i

  have hbox : ∀ i : Fin T.card, (0 : ℤ) ∈ Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1) :=
    fun i => Finset.mem_Icc.mpr ⟨by simp, by simp⟩
  have r1 := ArrayAlgGlue.sum_piFinset_prod_mul_prod_ite_eq_zero
    (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)) hbox g
  have r2 := fun p : T => ArrayAlgGlue.sum_piFinset_prod_mul_prod_erase_ite_mul
    (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)) hbox g (T.equivFin p)
    (fun n => 1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * n.natAbs))

  have hg0 : ∏ i : Fin T.card, g i 0 = ∏ v : T, G0 v.1 := by
    refine (Fintype.prod_equiv T.equivFin (fun v : T => G0 v.1) (fun i => g i 0) fun v => ?_).symm
    simp only [hg, hG0, Equiv.symm_apply_apply]
  have hgE : ∀ p : T, (∑ r ∈ Finset.Icc (-(ks (T.equivFin.symm (T.equivFin p)).1 : ℤ)) (ks (T.equivFin.symm (T.equivFin p)).1),
        g (T.equivFin p) r * (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * r.natAbs))) = GE p.1 := by
    intro p
    simp only [hg, hGE, Equiv.symm_apply_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hgerase : ∀ p : T, ∏ i ∈ Finset.univ.erase (T.equivFin p), g i 0 = ∏ i ∈ Finset.univ.erase p, G0 i.1 := by
    intro p
    symm
    calc ∏ i ∈ Finset.univ.erase p, G0 i.1
        = ∏ v ∈ Finset.univ.erase p, g (T.equivFin.toEmbedding v) 0 := by
          refine Finset.prod_congr rfl fun v _ => ?_
          simp only [hg, hG0, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
      _ = ∏ x ∈ (Finset.univ.erase p).map T.equivFin.toEmbedding, g x 0 :=
          (Finset.prod_map (Finset.univ.erase p) T.equivFin.toEmbedding (fun x => g x 0)).symm
      _ = ∏ i ∈ Finset.univ.erase (T.equivFin p), g i 0 := by
          rw [Finset.map_erase, Finset.map_univ_equiv]; rfl
  have fin : ∀ p : T, (c₁ p.1 * GE p.1 + c₂ p.1 * G0 p.1) * ∏ i ∈ Finset.univ.erase p, G0 i.1 =
      c₁ p.1 * ((∑ r ∈ Finset.Icc (-(ks (T.equivFin.symm (T.equivFin p)).1 : ℤ)) (ks (T.equivFin.symm (T.equivFin p)).1),
        g (T.equivFin p) r * (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * r.natAbs))) *
        ∏ i ∈ Finset.univ.erase (T.equivFin p), g i 0) + c₂ p.1 * ∏ i : Fin T.card, g i 0 := by
    intro p
    rw [hgE p, hgerase p, hg0, ← Finset.mul_prod_erase (Finset.univ : Finset T) (fun i : T => G0 i.1) (Finset.mem_univ p)]
    ring

  have lin : ∀ cm X Y : ℂ, cm * (Λ * ((R : ℂ) * X + Y) + κ₀ * X) = Λ * (R : ℂ) * (cm * X) + Λ * (cm * Y) + κ₀ * (cm * X) := by
    intros; ring
  simp only [lin]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

  simp only [hA, hB, hG0, hGE] at e1 e2 fin hg0
  simp only [hg] at r1 r2 fin hg0
  rw [e1, e2, r1]
  simp only [r2, fin]
  simp only [hg0]
  ring

end S_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
end P2MW
export P2MW.S_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge (solution)
