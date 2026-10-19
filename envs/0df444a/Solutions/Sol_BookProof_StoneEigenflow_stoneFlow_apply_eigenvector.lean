-- Prove2me | solution 1 for BookProof.StoneEigenflow.stoneFlow_apply_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:12:27.927892+00:00
-- url     : https://prove2.me/submissions/d44ebea7-f1d7-4eca-b6a4-1b06351a5429

-- Generated from ChapterStoneEigenflow.lean — solution of BookProof.StoneEigenflow.stoneFlow_apply_eigenvector
import Mathlib
import Definitions.Def_ChapterStoneEigenflow
import Theorems.Thm_BookProof_FriedrichsSquare_IsFriedrichsSqExtension_symmetric
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterStoneResolvent
open BookProof.StoneEigenflow



open scoped InnerProductSpace


open BookProof.ChapterUnitaryTransport BookProof.EsaClosure BookProof.FarisLavine
open BookProof.ChapterStoneResolvent BookProof.StoneBridge
open BookProof.StoneBridge
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (hU : IsStoneFlow T U) {x : F} (hx : x ∈ T.domain) {lam : ℝ}
    (hev : T.op ⟨x, hx⟩ = (lam : ℂ) • x) (t : ℝ) :
    U t x = Complex.exp (-(Complex.I * lam * t)) • x := by

  obtain ⟨hU0, -, hiso, hflow⟩ := hU
  set φ : ℝ → ℂ := fun s => ⟪x, U s x⟫_ℂ with hφ
  have hderiv : ∀ s : ℝ, HasDerivAt φ (-(Complex.I * lam) * φ s) s := by
    intro s
    obtain ⟨h, hd⟩ := hflow x hx s
    have hL : HasDerivAt φ (⟪x, (-Complex.I) • T.op ⟨U s x, h⟩⟫_ℂ) s := by
      have hthis := ((innerSL ℂ x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hd
      have hfun : (fun w : F => ⟪x, w⟫_ℂ) ∘ (fun s : ℝ => (U s) x)
          = fun s => ⟪x, (U s) x⟫_ℂ := rfl
      rw [hφ]
      rw [← hfun]
      exact hthis
    have hval : (⟪x, (-Complex.I) • T.op ⟨U s x, h⟩⟫_ℂ) = -(Complex.I * lam) * φ s := by
      rw [inner_smul_right]
      have hs := T.symmetric ⟨x, hx⟩ ⟨U s x, h⟩
      simp only at hs
      rw [hev] at hs
      rw [← hs, inner_smul_left]
      simp [hφ]
      ring
    rwa [hval] at hL
  -- `g s = e^{iλs} φ(s)` has vanishing derivative, hence is constant.
  set g : ℝ → ℂ := fun s => Complex.exp (Complex.I * lam * s) * φ s with hg
  have hgderiv : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => Complex.I * lam * (s : ℂ)) (Complex.I * lam) s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * lam))
    have h2 := (h1.cexp).mul (hderiv s)
    have hm : (fun x : ℝ => Complex.exp (Complex.I * lam * x)) * φ
        = fun s : ℝ => Complex.exp (Complex.I * lam * s) * φ s := rfl
    simp [hg]
    rw [← hm]
    exact h2.congr_deriv (by ring)
  have hconst : g t = g 0 :=
    is_const_of_fderiv_eq_zero (fun s => (hgderiv s).differentiableAt)
      (fun s => by simpa using (hgderiv s).hasFDerivAt.fderiv) t 0
  set e : ℂ := Complex.exp (-(Complex.I * lam * t)) with he
  have hg0 : g 0 = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    simp [hg, hφ, hU0, inner_self_eq_norm_sq_to_K]
  have hexp : Complex.exp (Complex.I * lam * t) * e = 1 := by
    rw [he, ← Complex.exp_add]; simp
  have hφt : φ t = e * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have hct : Complex.exp (Complex.I * lam * t) * φ t = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [← hg0, ← hconst]
    calc φ t = (e * Complex.exp (Complex.I * lam * t)) * φ t := by
          rw [mul_comm e, hexp]; ring
      _ = e * ((‖x‖ ^ 2 : ℝ) : ℂ) := by rw [mul_assoc, hct]
  have hnorme : ‖e‖ = 1 := by
    rw [he, Complex.norm_exp]; simp
  have hconj : (starRingEnd ℂ) e * e = 1 := by
    rw [he, ← Complex.exp_conj, ← Complex.exp_add]; simp
  have hinner : ⟪U t x, e • x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, ← inner_conj_symm]
    change e * (starRingEnd ℂ) (φ t) = _
    rw [hφt, map_mul]
    calc e * ((starRingEnd ℂ) e * (starRingEnd ℂ) ((‖x‖ ^ 2 : ℝ) : ℂ))
        = ((starRingEnd ℂ) e * e) * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.conj_ofReal]; ring
      _ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by rw [hconj]; ring
  have hz : ‖U t x - e • x‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hinner, hiso, norm_smul, hnorme,
      show RCLike.re ((‖x‖ ^ 2 : ℝ) : ℂ) = ‖x‖ ^ 2 from Complex.ofReal_re _]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz))
