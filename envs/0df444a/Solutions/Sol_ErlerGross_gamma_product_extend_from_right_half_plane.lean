-- Prove2me | solution 1 for ErlerGross.gamma_product_extend_from_right_half_plane
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T20:48:51.013151+00:00
-- url     : https://prove2.me/submissions/ee59a246-5d67-42be-8b86-aee5331a164d

import Mathlib

open Filter Topology

theorem solution (n : Nat) (hn : 0 < n)
    (c : ℂ) (hc : c ≠ 0)
    (hpos : ∀ z : ℂ, 0 < z.re →
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : ℂ) / n)) =
        c * Complex.exp (-(n : ℂ) * z * (Real.log n : ℂ)) *
          Complex.Gamma ((n : ℂ) * z)) :
    ∀ z : ℂ,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (z + (k : ℂ) / n)) =
        c * Complex.exp (-(n : ℂ) * z * (Real.log n : ℂ)) *
          Complex.Gamma ((n : ℂ) * z) := by
  classical
  let F : ℂ → ℂ := fun z =>
    ∏ k ∈ Finset.range n, (Complex.Gamma (z + (k : ℂ) / n))⁻¹
  let G : ℂ → ℂ := fun z =>
    (Complex.Gamma ((n : ℂ) * z))⁻¹ *
      (Complex.exp (-(n : ℂ) * z * (Real.log n : ℂ)))⁻¹ * c⁻¹
  have hInv : Differentiable ℂ (fun w : ℂ => (Complex.Gamma w)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have hprod : Differentiable ℂ
      (∏ k ∈ Finset.range n, fun z : ℂ => (Complex.Gamma (z + (k : ℂ) / n))⁻¹) :=
    Differentiable.finsetProd (fun k hk =>
      hInv.comp (differentiable_id.add_const ((k : ℂ) / n)))
  have hEq : F = ∏ k ∈ Finset.range n,
      (fun z : ℂ => (Complex.Gamma (z + (k : ℂ) / n))⁻¹) := by
    funext z
    simp [F]
  have hFD : Differentiable ℂ F := hEq ▸ hprod
  have hExp : Differentiable ℂ (fun z : ℂ => Complex.exp (-(n : ℂ) * z * (Real.log n : ℂ))) := by
    fun_prop
  have hExpNe : ∀ z : ℂ, Complex.exp (-(n : ℂ) * z * (Real.log n : ℂ)) ≠ 0 := by
    intro z
    exact Complex.exp_ne_zero _
  have hArg : Differentiable ℂ (fun z : ℂ => (n : ℂ) * z) := by
    fun_prop
  have hcInv : Differentiable ℂ (fun _ : ℂ => c⁻¹) := differentiable_const (c⁻¹)
  have hGD : Differentiable ℂ G := by
    unfold G
    exact ((hInv.comp hArg).mul (hExp.inv hExpNe)).mul hcInv
  have hFA : AnalyticOnNhd ℂ F Set.univ :=
    (hFD.differentiableOn).analyticOnNhd isOpen_univ
  have hGA : AnalyticOnNhd ℂ G Set.univ :=
    (hGD.differentiableOn).analyticOnNhd isOpen_univ
  have hposneigh : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    norm_num
  have hnear : F =ᶠ[𝓝 (1 : ℂ)] G := by
    filter_upwards [hposneigh] with z hz
    have hh := congrArg (fun w : ℂ => w⁻¹) (hpos z hz)
    simpa [F, G, Finset.prod_inv_distrib, mul_inv, mul_assoc] using hh
  have hFG : F = G := by
    exact funext fun z => hFA.eqOn_of_preconnected_of_eventuallyEq hGA
      isPreconnected_univ (Set.mem_univ (1 : ℂ)) hnear (Set.mem_univ z)
  intro z
  have hh := congrArg (fun w : ℂ => w⁻¹) (congrFun hFG z)
  simpa [F, G, Finset.prod_inv_distrib, mul_inv, mul_assoc] using hh
