-- Prove2me | solution 1 for DeficitAtMax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:26:56.302813+00:00
-- url     : https://prove2.me/submissions/b64e7c8e-985d-46ce-925b-ab0b6b70645a

module
public import Definitions.Def_PHarmonicPoly_TraceIdentity
public import Definitions.Def_PHarmonicPoly_GreatCircleTrigPoly
public import Definitions.Def_PHarmonicPoly_GreatCircleSecondDeriv
public import Definitions.Def_PHarmonicPoly_DeficitBound
public import Definitions.Def_PHarmonicPoly_DeficitAtMax
public import Theorems.Thm_DeficitBound
public import Theorems.Thm_GreatCircleSecondDeriv
public import Theorems.Thm_GreatCircleTrigPoly
public import Theorems.Thm_MaxPointDerivatives
public import Theorems.Thm_TraceIdentity


set_option autoImplicit false
@[expose] public section
public section
open MvPolynomial
theorem _root_.solution {n m : ℕ} (hn : 3 ≤ n) (hm : 2 ≤ m) {p : ℝ}
    (hp : (n : ℝ) - 1 / 13 ≤ p)
    {P : MvPolynomial (Fin n) ℝ} (hhom : P.IsHomogeneous m)
    {e : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hmax : MvPolynomial.eval (fun i => e i) P = 1)
    (hbd : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ = 1 →
      |MvPolynomial.eval (fun i => y i) P| ≤ 1)
    (hE : EpAlg p P = 0) :
    p ≤ (n : ℝ) ∧
      ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
        0 ≤ iteratedFDeriv ℝ 2
              (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
              ![v, v] + (m : ℝ) * ((m : ℝ) - 1)
        ∧ iteratedFDeriv ℝ 2
              (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
              ![v, v] + (m : ℝ) * ((m : ℝ) - 1)
            ≤ ((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1))
        ∧ -1 ≤ MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P
        ∧ MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P
            ≤ -1 + Real.pi ^ 2 * ((n : ℝ) - p) / 2
        ∧ 8 / 13 < -(MvPolynomial.eval (fun i =>
              (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
                EuclideanSpace ℝ (Fin n)) i) P) := by
  classical
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmm : (0 : ℝ) < (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
  -- Step 0a
  have hdeg : P.totalDegree ≤ m := by
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · exact le_of_eq (hhom.totalDegree hP0)
  -- Step 0b
  have hsph : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      ∀ t : ℝ, ‖(Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    intro v hv hev t
    have hsq : ‖(Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, he, hv,
        real_inner_smul_left, real_inner_smul_right, hev]
      simp only [Real.norm_eq_abs, mul_one, mul_zero, sq_abs]
      nlinarith [Real.sin_sq_add_cos_sq t]
    nlinarith [hsq, norm_nonneg (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n))]
  -- Step 2
  have hgrad := (MaxPointDerivatives (n := n) (m := m) (by omega) hhom he hmax hbd).1
  have hsec : ∀ v : EuclideanSpace ℝ (Fin n),
      iteratedDeriv 2 (fun s : ℝ => MvPolynomial.eval
          (fun i => (Real.cos s • e + Real.sin s • v : EuclideanSpace ℝ (Fin n)) i) P) 0
        = iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![v, v]
          - (m : ℝ) := by
    intro v
    have h := GreatCircleSecondDeriv P 0 e v 0
    simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, zero_add,
      neg_zero] at h
    rw [hgrad] at h
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he] at h
    simpa using h
  -- 1 - cos(π/m) > 0
  have hhpos : 0 < Real.pi / (m : ℝ) := by positivity
  have hhle : Real.pi / (m : ℝ) ≤ Real.pi := by
    exact div_le_self Real.pi_pos.le (by linarith)
  have hcospos : 0 < 1 - Real.cos (Real.pi / (m : ℝ)) := by
    have h := Real.strictAntiOn_cos (Set.mem_Icc.mpr ⟨le_refl 0, Real.pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hhpos.le, hhle⟩) hhpos
    rw [Real.cos_zero] at h
    linarith
  -- Steps 1, 3, 4 bundled, for an arbitrary unit v orthogonal to e
  have hpkg : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ = 1 → inner ℝ e v = (0 : ℝ) →
      (0 ≤ 1 + MvPolynomial.eval (fun i =>
            (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
              EuclideanSpace ℝ (Fin n)) i) P)
      ∧ (1 + MvPolynomial.eval (fun i =>
            (Real.cos (Real.pi / m) • e + Real.sin (Real.pi / m) • v :
              EuclideanSpace ℝ (Fin n)) i) P
          ≤ (iteratedFDeriv ℝ 2
                (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
                ![v, v] + (m : ℝ) * ((m : ℝ) - 1)) * (1 - Real.cos (Real.pi / m)))
      ∧ ((iteratedFDeriv ℝ 2
                (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
                ![v, v] + (m : ℝ) * ((m : ℝ) - 1)) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * (iteratedFDeriv ℝ 2
                (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
                ![v, v] + (m : ℝ) * ((m : ℝ) - 1)) / (2 * (m : ℝ) ^ 2))
      ∧ 0 ≤ iteratedFDeriv ℝ 2
              (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
              ![v, v] + (m : ℝ) * ((m : ℝ) - 1) := by
    intro v hv hev
    have hTP : TrigPolyLe m (fun t => MvPolynomial.eval
        (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P) :=
      GreatCircleTrigPoly hdeg e v
    have hTbd : ∀ t : ℝ, |MvPolynomial.eval
        (fun i => (Real.cos t • e + Real.sin t • v : EuclideanSpace ℝ (Fin n)) i) P| ≤ 1 :=
      fun t => hbd _ (hsph v hv hev t)
    have hT0 : MvPolynomial.eval
        (fun i => (Real.cos 0 • e + Real.sin 0 • v : EuclideanSpace ℝ (Fin n)) i) P = 1 := by
      simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
      exact hmax
    have hDB := DeficitBound hm hTP hTbd hT0
    rw [hsec v] at hDB
    have hrw : (m : ℝ) ^ 2 + (iteratedFDeriv ℝ 2
          (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![v, v]
          - (m : ℝ))
        = iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![v, v]
          + (m : ℝ) * ((m : ℝ) - 1) := by ring
    rw [hrw] at hDB
    obtain ⟨⟨hA, _⟩, ⟨hB, _⟩, hC⟩ := hDB
    refine ⟨hA, hB, hC, ?_⟩
    nlinarith [hA, hB, hcospos]
  -- Step 5: p ≤ n
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  have hpn : p ≤ (n : ℝ) := by
    set i₀ : Fin n := ⟨0, by omega⟩ with hi0
    have horth : Orthonormal ℝ (({i₀} : Set (Fin n)).domRestrict (fun _ => e)) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_singleton_iff] at hi hj
      subst hi; subst hj
      simp [Set.domRestrict, he]
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    have hb0 : b i₀ = e := hb i₀ rfl
    have htr := TraceIdentity (by omega : 1 ≤ m) hhom he hmax hbd hE b hb0
    have hsum : 0 ≤ ∑ i ∈ Finset.univ.erase i₀,
        (iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
            ![b i, b i] + (m : ℝ) * ((m : ℝ) - 1)) := by
      refine Finset.sum_nonneg (fun i hi => ?_)
      have hine : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      have hbi : ‖b i‖ = 1 := b.orthonormal.1 i
      have hperp : inner ℝ e (b i) = (0 : ℝ) := by
        rw [← hb0]; exact b.orthonormal.2 (Ne.symm hine)
      exact (hpkg (b i) hbi hperp).2.2.2
    rw [htr] at hsum
    nlinarith [hsum, hmm]
  refine ⟨hpn, ?_⟩
  intro v hv hev
  obtain ⟨hA, hB, hC, hD⟩ := hpkg v hv hev
  -- Step 6
  have hub : iteratedFDeriv ℝ 2
        (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![v, v]
        + (m : ℝ) * ((m : ℝ) - 1)
      ≤ ((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1)) := by
    set i₀ : Fin n := ⟨0, by omega⟩ with hi0
    set i₁ : Fin n := ⟨1, by omega⟩ with hi1
    have hne : i₀ ≠ i₁ := by rw [hi0, hi1]; simp
    set f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => if i = i₀ then e else v with hf
    have hve : inner ℝ v e = (0 : ℝ) := by rw [real_inner_comm]; exact hev
    have horth : Orthonormal ℝ (({i₀, i₁} : Set (Fin n)).domRestrict f) := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> subst hi <;> subst hj <;>
        simp only [Set.domRestrict, hf, Subtype.mk.injEq] <;>
        simp [hne, hne.symm, he, hv, hev, hve]
    obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
    have hb0 : b i₀ = e := by rw [hb i₀ (by simp), hf]; simp
    have hb1 : b i₁ = v := by rw [hb i₁ (by simp), hf]; simp [hne.symm]
    have htr := TraceIdentity (by omega : 1 ≤ m) hhom he hmax hbd hE b hb0
    have hnn : ∀ i ∈ Finset.univ.erase i₀,
        0 ≤ iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
            ![b i, b i] + (m : ℝ) * ((m : ℝ) - 1) := by
      intro i hi
      have hine : i ≠ i₀ := (Finset.mem_erase.mp hi).1
      have hbi : ‖b i‖ = 1 := b.orthonormal.1 i
      have hperp : inner ℝ e (b i) = (0 : ℝ) := by
        rw [← hb0]; exact b.orthonormal.2 (Ne.symm hine)
      exact (hpkg (b i) hbi hperp).2.2.2
    have hmem : i₁ ∈ Finset.univ.erase i₀ :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    have hle := Finset.single_le_sum hnn hmem
    rw [htr, hb1] at hle
    exact hle
  have hdelta : (0 : ℝ) ≤ (n : ℝ) - p := by linarith [hpn]
  have hstep : Real.pi ^ 2 * (iteratedFDeriv ℝ 2
        (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e ![v, v]
        + (m : ℝ) * ((m : ℝ) - 1)) / (2 * (m : ℝ) ^ 2)
      ≤ Real.pi ^ 2 * ((n : ℝ) - p) / 2 := by
    have hpi2nn : (0 : ℝ) ≤ Real.pi ^ 2 := sq_nonneg _
    have hA1 : 0 ≤ Real.pi ^ 2 * (((n : ℝ) - p) * ((m : ℝ) * ((m : ℝ) - 1))
        - (iteratedFDeriv ℝ 2
            (fun x : EuclideanSpace ℝ (Fin n) => MvPolynomial.eval (fun i => x i) P) e
            ![v, v] + (m : ℝ) * ((m : ℝ) - 1))) :=
      mul_nonneg hpi2nn (by linarith [hub])
    have hB1 : 0 ≤ Real.pi ^ 2 * (((n : ℝ) - p) * (m : ℝ)) :=
      mul_nonneg hpi2nn (mul_nonneg hdelta hmpos.le)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hA1, hB1]
  refine ⟨hD, hub, by linarith [hA], ?_, ?_⟩
  -- Step 7
  · linarith [hA, hB, hC, hstep]
  -- Step 8
  · have hd13 : (n : ℝ) - p ≤ 1 / 13 := by linarith [hp]
    have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    nlinarith [hA, hB, hC, hstep, hpi2, hdelta, hd13]
