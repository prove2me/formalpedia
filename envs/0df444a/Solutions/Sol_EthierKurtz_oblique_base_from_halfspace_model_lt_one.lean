-- Prove2me | solution 1 for EthierKurtz.oblique_base_from_halfspace_model_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T23:27:53.264444+00:00
-- url     : https://prove2.me/submissions/f6e0a64c-631f-4102-b860-79bb9dec522d

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_COnceHolder
import Definitions.Def_EthierKurtz_CTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Theorems.Thm_EthierKurtz_oblique_global_solver_from_pieces
import Theorems.Thm_EthierKurtz_oblique_local_pieces_from_boundary_solvers
import Theorems.Thm_EthierKurtz_oblique_boundary_local_solver
import Theorems.Thm_EthierKurtz_oblique_halfspace_variable_coeff_model
import Theorems.Thm_EthierKurtz_oblique_c2mu_extension_package
import Theorems.Thm_EthierKurtz_oblique_boundary_flattening_charts

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open scoped BoundedContinuousFunction
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ (n : ℕ) (hd : 2 ≤ n + 1)
        (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
        (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
        (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) (hμ1 : μ < 1)
        (hboundary : EthierKurtz.BoundaryCTwiceHolder Ω μ)
        (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (hc : ∀ i, EthierKurtz.BoundaryCOnceHolder Ω μ (fun x => c x i))
        (hnormal : ∀ x ∈ frontier Ω, EthierKurtz.IsOutwardUnitNormal Ω x (normal x))
        (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
          ε ≤ ∑ i, c x i * normal x i),
        ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
          HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
            ∃ fg ∈ EthierKurtz.obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
              lam₀ • fg.1 - fg.2 = h := by
  intro n hd Ω hbounded hconnected hopen μ hμ hμ1 hboundary c normal hc hnormal hoblique
  have hV := EthierKurtz.oblique_halfspace_variable_coeff_model (n + 1) μ hμ.1 hμ1
  have hP := EthierKurtz.oblique_c2mu_extension_package (n + 1) μ hμ.1 hμ1
  have hch := EthierKurtz.oblique_boundary_flattening_charts n μ hμ.1 hμ1 hP Ω hopen hboundary c normal hc hnormal hoblique
  have hploc := EthierKurtz.oblique_boundary_local_solver (n + 1) Ω μ hμ.1 hμ1 c hV hch
  have hpiece := EthierKurtz.oblique_local_pieces_from_boundary_solvers (n + 1) (Nat.succ_pos n) Ω hopen μ hμ.1 hμ1 c hV hploc
  exact EthierKurtz.oblique_global_solver_from_pieces (n + 1) Ω hopen hbounded μ hμ.1 hμ1 c hpiece
