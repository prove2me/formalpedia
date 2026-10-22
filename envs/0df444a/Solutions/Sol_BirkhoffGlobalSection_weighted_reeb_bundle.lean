-- Prove2me | solution 1 for BirkhoffGlobalSection.weighted_reeb_bundle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T12:48:59.850702+00:00
-- url     : https://prove2.me/submissions/0b0dad14-5aa0-4aff-b748-63c8a18fea50

import Theorems.Thm_BirkhoffGlobalSection_weighted_sphere_contact_geometry
import Theorems.Thm_BirkhoffGlobalSection_gauge_inverse_contact_weight
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false



private theorem coordinateExpansion (L : Phase →L[ℝ] ℝ) (v : Phase) :
    L v = v 0 * L (coordinateVector 0) + v 1 * L (coordinateVector 1) +
      v 2 * L (coordinateVector 2) + v 3 * L (coordinateVector 3) := by
  have hv : v = v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  calc
    L v = L (v 0 • coordinateVector 0 + v 1 • coordinateVector 1 +
      v 2 • coordinateVector 2 + v 3 • coordinateVector 3) := congrArg L hv
    _ = _ := by simp

private theorem weighted_reeb_formula_algebra (u : Phase) (hu : u ∈ unitThreeSphere)
    (a : ℝ) (ha : 0 < a) (L : Phase →L[ℝ] ℝ) :
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := (a ^ 2)⁻¹ • ((2 * a + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
      a * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        L R * phaseRadialContact u w - L w * phaseRadialContact u R -
          a * phaseSymplecticForm R w = 0) := by
  let D : Phase → Phase → ℝ := fun v w =>
    v 0 * w 0 + v 1 * w 1 + v 2 * w 2 + v 3 * w 3
  let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
  let g : Phase := fun i => L (coordinateVector i)
  have hgrad (v : Phase) : D g v = L v := by
    rw [coordinateExpansion L v]
    dsimp [D, g]
    ring
  have hunit : D u u = 1 := by
    have hQ : zNormSq u + wNormSq u = 1 := hu
    dsimp [D]
    simp [zNormSq, wNormSq] at hQ
    nlinarith [hQ]
  have horth (v : Phase) : D v (J v) = 0 := by simp [D, J]; ring
  have hswap (v w : Phase) : D v (J w) = -D (J v) w := by simp [D, J]; ring
  have hωJ (v w : Phase) : phaseSymplecticForm (J v) w = D v w := by
    simp [D, J, phaseSymplecticForm]
    ring
  have hαJ (v : Phase) : phaseRadialContact u (J v) = D v u / 2 := by
    simp [D, J, phaseRadialContact, phaseSymplecticForm]
    ring
  have hαself : phaseRadialContact u u = 0 := by
    simp [phaseRadialContact, phaseSymplecticForm]
    ring
  have hLJg : L (J g) = 0 := by rw [← hgrad, horth]
  let V : Phase := (2 * a + L u) • J u - J g - L (J u) • u
  have htV : D u V = 0 := by
    have heq : D u V = (2 * a + L u) * D u (J u) -
        D u (J g) - L (J u) * D u u := by
      simp [D, V]
      ring
    rw [heq, horth, hswap]
    have hg : D (J u) g = L (J u) := by rw [← hgrad]; dsimp [D]; ring
    rw [hg, hunit]
    ring
  have hαV : phaseRadialContact u V = a := by
    have heq : phaseRadialContact u V =
        (2 * a + L u) * phaseRadialContact u (J u) -
          phaseRadialContact u (J g) - L (J u) * phaseRadialContact u u := by
      simp [V, phaseRadialContact, phaseSymplecticForm]
      ring
    rw [heq, hαJ, hαJ, hunit, hgrad, hαself]
    ring
  have hLV : L V = 2 * a * L (J u) := by
    simp only [V, map_sub, map_smul, smul_eq_mul]
    rw [hLJg]
    ring
  have hωV (w : Phase) (hw : D u w = 0) :
      phaseSymplecticForm V w = -L w + 2 * L (J u) * phaseRadialContact u w := by
    have heq : phaseSymplecticForm V w =
        (2 * a + L u) * phaseSymplecticForm (J u) w -
          phaseSymplecticForm (J g) w - L (J u) * phaseSymplecticForm u w := by
      simp [V, phaseSymplecticForm]
      ring
    rw [heq, hωJ, hωJ, hw, hgrad]
    simp [phaseRadialContact]
    ring
  let R : Phase := (a ^ 2)⁻¹ • V
  have hαR : phaseRadialContact u R = (a ^ 2)⁻¹ * a := by
    have heq : phaseRadialContact u R = (a ^ 2)⁻¹ * phaseRadialContact u V := by
      simp [R, phaseRadialContact, phaseSymplecticForm]
      ring
    rw [heq, hαV]
  change (D u R = 0) ∧ (a * phaseRadialContact u R = 1) ∧
    (∀ w : Phase, D u w = 0 →
      L R * phaseRadialContact u w - L w * phaseRadialContact u R -
        a * phaseSymplecticForm R w = 0)
  refine ⟨?_, ?_, ?_⟩
  · have heq : D u R = (a ^ 2)⁻¹ * D u V := by simp [D, R]; ring
    rw [heq, htV, mul_zero]
  · rw [hαR]
    field_simp [ha.ne']
  · intro w hw
    have hωR : phaseSymplecticForm R w = (a ^ 2)⁻¹ * phaseSymplecticForm V w := by
      simp [R, phaseSymplecticForm]
      ring
    have hLR : L R = (a ^ 2)⁻¹ * L V := by simp [R]
    rw [hLR, hLV, hαR, hωR, hωV w hw]
    ring

private theorem weighted_sphere_reeb_formula (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let L := fderiv ℝ f u
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := ((f u) ^ 2)⁻¹ •
      ((2 * f u + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
    (f u * phaseRadialContact u R = 1) ∧
    (∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by
  have h := weighted_reeb_formula_algebra u hu (f u) hf (fderiv ℝ f u)
  refine ⟨h.1, h.2.1, ?_⟩
  intro w hw
  rw [weighted_radial_contact_exterior_derivative f u _ w hdf]
  exact h.2.2 w hw

private theorem weighted_sphere_reeb_exists_unique (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u) :
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by
  let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
  let L := fderiv ℝ f u
  let g : Phase := fun i => L (coordinateVector i)
  let R : Phase := ((f u) ^ 2)⁻¹ •
    ((2 * f u + L u) • J u - J g - L (J u) • u)
  have h := weighted_reeb_formula_algebra u hu (f u) hf (fderiv ℝ f u)
  have htR : u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 := h.1
  have hαR : f u * phaseRadialContact u R = 1 := h.2.1
  have hdR (w : Phase)
      (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) :
      fderiv ℝ f u R * phaseRadialContact u w -
        fderiv ℝ f u w * phaseRadialContact u R - f u * phaseSymplecticForm R w = 0 :=
    h.2.2 w hw
  have hdR' (w : Phase)
      (hw : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0) :
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0 := by
    rw [weighted_radial_contact_exterior_derivative f u R w hdf]
    exact hdR w hw
  refine ⟨R, ⟨htR, hαR, hdR'⟩, ?_⟩
  intro S hS
  have ht : u 0 * (S - R) 0 + u 1 * (S - R) 1 +
      u 2 * (S - R) 2 + u 3 * (S - R) 3 = 0 := by
    simp only [Pi.sub_apply]
    nlinarith [hS.1, htR]
  have hαsub : phaseRadialContact u (S - R) =
      phaseRadialContact u S - phaseRadialContact u R := by
    simp [phaseRadialContact, phaseSymplecticForm]
    ring
  have hα : f u * phaseRadialContact u (S - R) = 0 := by
    rw [hαsub]
    nlinarith [hS.2.1, hαR]
  have hz := (weighted_sphere_contact_geometry f u hu hf hdf).1.2 (S - R) ht hα
  apply sub_eq_zero.mp
  apply hz
  intro w hw _
  rw [weighted_radial_contact_exterior_derivative f u (S - R) w hdf]
  have hs := hS.2.2 w hw
  rw [weighted_radial_contact_exterior_derivative f u S w hdf] at hs
  have hr := hdR w hw
  have hωsub : phaseSymplecticForm (S - R) w =
      phaseSymplecticForm S w - phaseSymplecticForm R w := by
    simp [phaseSymplecticForm]
    ring
  rw [map_sub, hαsub, hωsub]
  nlinarith [hs, hr]

private theorem weighted_sphere_reeb_formula_smooth (f : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f u) (hpos : 0 < f u) :
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase → Phase := fun x i => fderiv ℝ f x (coordinateVector i)
    let R : Phase → Phase := fun x => ((f x) ^ 2)⁻¹ •
      ((2 * f x + fderiv ℝ f x x) • J x - J (g x) -
        (fderiv ℝ f x (J x)) • x)
    ContDiffAt ℝ ∞ R u := by
  let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
  have hJ : ContDiff ℝ ∞ J := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp [J] <;> fun_prop
  have hDf : ContDiffAt ℝ ∞ (fun x => fderiv ℝ f x) u := hf.fderiv_right (by simp)
  have hg : ContDiffAt ℝ ∞ (fun x i => fderiv ℝ f x (coordinateVector i)) u := by
    apply contDiffAt_pi.mpr
    intro i
    exact hDf.clm_apply contDiffAt_const
  have hscale : ContDiffAt ℝ ∞ (fun x => ((f x) ^ 2)⁻¹) u :=
    (hf.pow 2).inv (pow_ne_zero _ hpos.ne')
  have htwo : ContDiffAt ℝ ∞ (fun x => 2 * f x) u := contDiffAt_const.mul hf
  exact hscale.smul
    (((htwo.add (hDf.clm_apply contDiffAt_id)).smul hJ.contDiffAt).sub
      (hJ.contDiffAt.comp u hg) |>.sub ((hDf.clm_apply hJ.contDiffAt).smul contDiffAt_id))

private theorem gauge_inverse_sphere_reeb_exists_unique (B : Set Phase)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u) :
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0) := by
  have h := gauge_inverse_contact_weight B h0 hb u hu hG
  exact weighted_sphere_reeb_exists_unique _ u hu h.1
    (h.2.1.differentiableAt (by simp))

theorem solution :
(∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let L := fderiv ℝ f u
    let g : Phase := fun i => L (coordinateVector i)
    let R : Phase := ((f u) ^ 2)⁻¹ •
      ((2 * f u + L u) • J u - J g - L (J u) • u)
    (u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0) ∧
    (f u * phaseRadialContact u R = 1) ∧
    (∀ w : Phase,
      u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
      fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
        fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) ∧
(∀ (f : Phase → ℝ) (u : Phase)
    (hu : u ∈ unitThreeSphere) (hf : 0 < f u) (hdf : DifferentiableAt ℝ f u),
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) ∧
(∀ (f : Phase → ℝ) (u : Phase)
    (hf : ContDiffAt ℝ ∞ f u) (hpos : 0 < f u),
    let J : Phase → Phase := fun v => ![v 2, v 3, -v 0, -v 1]
    let g : Phase → Phase := fun x i => fderiv ℝ f x (coordinateVector i)
    let R : Phase → Phase := fun x => ((f x) ^ 2)⁻¹ •
      ((2 * f x + fderiv ℝ f x x) • J x - J (g x) -
        (fderiv ℝ f x (J x)) • x)
    ContDiffAt ℝ ∞ R u) ∧
(∀ (B : Set Phase)
    (h0 : B ∈ 𝓝 (0 : Phase)) (hb : Bornology.IsVonNBounded ℝ B)
    (u : Phase) (hu : u ∈ unitThreeSphere)
    (hG : ContDiffAt ℝ ∞ (fun x : Phase => (gauge B x)⁻¹ • x) u),
    let G : Phase → Phase := fun x => (gauge B x)⁻¹ • x
    let f : Phase → ℝ := fun x => zNormSq (G x) + wNormSq (G x)
    ∃! R : Phase,
      u 0 * R 0 + u 1 * R 1 + u 2 * R 2 + u 3 * R 3 = 0 ∧
      f u * phaseRadialContact u R = 1 ∧
      (∀ w : Phase,
        u 0 * w 0 + u 1 * w 1 + u 2 * w 2 + u 3 * w 3 = 0 →
        fderiv ℝ (fun x => f x * phaseRadialContact x w) u R -
          fderiv ℝ (fun x => f x * phaseRadialContact x R) u w = 0)) := by
  exact ⟨@weighted_sphere_reeb_formula, ⟨@weighted_sphere_reeb_exists_unique, ⟨@weighted_sphere_reeb_formula_smooth, @gauge_inverse_sphere_reeb_exists_unique⟩⟩⟩
