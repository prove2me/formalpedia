-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_integrand_residue_real_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:22.271326+00:00
-- url     : https://prove2.me/submissions/1127ec25-a82d-40a7-aa1a-080afdda0f73

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {β : ℂ} (h0 : 0 < β.re) (h1 : β ≠ 1)
    (hLβ : DirichletCharacter.LFunction χ β = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A β ∧
      ∀ᶠ z in 𝓝[≠] β, DirichletCharacter.LFunction χ z ≠ 0 ∧
        Fchi χ y z - (-((y : ℂ) ^ β / (β * (β - 1)))) / (z - β) = A z := by
  have hLd := DirichletCharacter.differentiable_LFunction hχ
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hβ0 : β ≠ 0 := fun h => by rw [h] at h0; simp at h0
  set L := DirichletCharacter.LFunction χ with hLdef
  set g := dslope L β with hg
  have hgd : Differentiable ℂ g := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2 hLd.differentiableOn).differentiableAt
      Filter.univ_mem
  have hgβ : g β ≠ 0 := by rw [hg, dslope_same]; exact hd
  have hLz : ∀ z, L z = (z - β) * g z := by
    intro z
    have := sub_smul_dslope L β z
    rw [hLβ, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hderiv : ∀ z, deriv L z = g z + (z - β) * deriv g z := by
    intro z
    have hfun : L = fun z => (z - β) * g z := funext hLz
    have h1 : HasDerivAt (fun z => (z - β) * g z) (1 * g z + (z - β) * deriv g z) z :=
      ((hasDerivAt_id' z).sub_const β).mul (hgd z).hasDerivAt
    rw [hfun, h1.deriv]
    ring
  have hev : ∀ᶠ z in 𝓝[≠] β, z ≠ β ∧ g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 := by
    have h2 : ∀ᶠ z in 𝓝 β, g z ≠ 0 ∧ z ≠ 0 ∧ z ≠ 1 :=
      ((hgd β).continuousAt.eventually_ne hgβ).and
        ((show ∀ᶠ z in 𝓝 β, z ≠ 0 from isOpen_ne.mem_nhds hβ0).and
          (show ∀ᶠ z in 𝓝 β, z ≠ 1 from isOpen_ne.mem_nhds h1))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h2] with z hz hz'
    exact ⟨hz, hz'⟩
  set k : ℂ → ℂ := fun z => (y : ℂ) ^ z / (z * (z - 1)) with hk
  have hs : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1} := isOpen_ne.inter isOpen_ne
  have hβs : β ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := ⟨hβ0, h1⟩
  have hkd : DifferentiableOn ℂ k {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
    intro z hz
    have hz' : DifferentiableAt ℂ (fun w : ℂ => (y : ℂ) ^ w / (w * (w - 1))) z :=
      (DifferentiableAt.const_cpow (f := fun w => w) differentiableAt_id (Or.inl hy')).div
        (by fun_prop) (mul_ne_zero hz.1 (sub_ne_zero.2 hz.2))
    exact hz'.differentiableWithinAt
  have hdk : DifferentiableAt ℂ (dslope k β) β :=
    ((Complex.differentiableOn_dslope (hs.mem_nhds hβs)).2 hkd).differentiableAt (hs.mem_nhds hβs)
  have hdg' : DifferentiableAt ℂ (deriv g) β := ((hgd.analyticAt β).deriv).differentiableAt
  refine ⟨fun z => -(dslope k β z) - deriv g z / g z * k z,
    hdk.neg.sub ((hdg'.div (hgd β) hgβ).mul ((hkd β hβs).differentiableAt (hs.mem_nhds hβs))), ?_⟩
  filter_upwards [hev] with z hz
  obtain ⟨hzβ, hgz, hz0, hz1⟩ := hz
  refine ⟨by rw [hLz]; exact mul_ne_zero (sub_ne_zero.2 hzβ) hgz, ?_⟩
  rw [dslope_of_ne _ hzβ, slope_def_field]
  have hLz' : ∀ z, DirichletCharacter.LFunction χ z = (z - β) * g z := hLz
  have hderiv' : ∀ z, deriv (DirichletCharacter.LFunction χ) z = g z + (z - β) * deriv g z := hderiv
  simp only [Fchi, negLD, hk, hderiv', hLz']
  field_simp [sub_ne_zero.2 hzβ, hgz, hz0, sub_ne_zero.2 hz1, hβ0, sub_ne_zero.2 h1]
  ring
end Formalism.ZeroFreeDirichlet
