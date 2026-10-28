-- Prove2me | solution 1 for CountingMatroid.Analysis.PositiveTimeTraceHarmonic.uncappedReturn_reversible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:36:22.183586+00:00
-- url     : https://prove2.me/submissions/22843259-7dbc-4e78-8704-70a93a13d279

/-
Required support modules adapted from meelgroup/arlib, commit 6262f60ad7556be62e94e87f6b5811cf299e7d94. Copyright and authorship notices are preserved in each file. Module import paths use CountingMatroidSupport; original declaration namespaces are retained for proof compatibility. Arlib is not a Lake package dependency.

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceHarmonic
import Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_CountingMatroid_Analysis_PositiveTimeTraceHarmonic_harmonic_extension_energy

namespace Arlib
end Arlib
namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `L²(μ)` functional calculus: expectation, inner product, variance

The functional-analytic side of the spectral-independence machinery is carried
out entirely in `L²(μ)` for a distribution `μ` on a finite type.  This module
sets up the three functionals used everywhere downstream and the identities
relating them.

* `Ex μ f` — expectation `∑ x, μ x * f x`.
* `ip μ f g` — inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`.
* `Var μ f` — variance `μ((f - μ(f))²)`.

The key identities, all elementary algebra over a finite sum:

* `Var_eq_ip_sub_sq` — `Var μ f = ⟪f, f⟫_μ - (μ f)²`;
* `Var_eq_pair` — the *pair form* `Var μ f = ½ ∑ x, ∑ y, μ x * μ y * (f x - f y)²`,
  which is what makes variance directly comparable to a Dirichlet form;
* `Var_eq_ip_self_of_mean_zero` — on mean-zero functions variance *is* the
  squared norm, which is why almost every proof below starts by centering `f`.

We also record that `ip μ` is a positive semidefinite symmetric bilinear form
(`isBilin_ip`, `ip_comm`, `ip_self_nonneg`), so that `psd_cauchy_schwarz` from
`Arlib.Probability.Bilinear` applies to it directly, together with the
lambda-form bilinearity lemmas (`ip_add_left`, `ip_smul_right`, …) that the
computations downstream actually rewrite with.

Two families of "support only" lemmas are here because *every* guarded-total
construction in the development produces a junk value off the support of the
averaging distribution: `Ex_congr_ae`, `Var_congr_ae` and `Ex_mono_of_ne_zero`
say that expectations, variances and their monotonicity see only the support.

Finally, `Ex_push_eq` and `ip_push_eq` transport `Ex` and `ip` along a
*rectangular* kernel; they involve no stationarity and are the bookkeeping that
makes the law of total variance (`Arlib.MarkovChains.Techniques.LevelVariance`)
a three-line
computation.

Everything here is proved from first principles with no `sorry`.
-/


namespace Arlib.Probability

open scoped BigOperators
open Finset

namespace FinDist

variable {Ω : Type*} [Fintype Ω]

/-! ## Expectation -/































/-! ## Inner product -/





theorem ip_comm (μ : FinDist Ω) (f g : Ω → ℝ) : ip μ f g = ip μ g f :=
  Finset.sum_congr rfl fun x _ => by ring













/-! ### Explicit bilinearity

`isBilin_ip` states bilinearity in terms of `Pi` addition and scalar
multiplication.  Most computations downstream are much smoother with the
arguments written as explicit lambdas, so we record that form too. -/











/-! ## Variance -/



























/-! ## Pushforwards

Two bookkeeping identities for a *rectangular* kernel `K : α → β`, both plain
`Finset.sum_comm`.  They are what makes the law of total variance a three-line
computation. -/

section Push

variable {α β : Type*} [Fintype α] [Fintype β]





end Push

/-! ## χ²-divergence -/













end FinDist

end Arlib.Probability

/-! ## Compatibility: the `Arlib.MarkovChains` spellings

These declarations used to live in `namespace Arlib.MarkovChains` (in
`Arlib/MarkovChains/Techniques/{Chain,Bilinear,Functional,TotalVariation,Coupling}.lean`).
They are not Markov-chain-specific and now live in `Arlib.Probability`.  The
aliases below reproduce the old fully-qualified names exactly, so that every
`Arlib/MarkovChains/**` module keeps resolving them unchanged.  New code should
use the `Arlib.Probability` names directly; this block can be deleted once the
`Arlib.MarkovChains` call sites have been migrated. -/

namespace Arlib.MarkovChains

export Arlib.Probability.FinDist (Ex       
        
  ip  ip_comm      
       Var  
       
        
      )

end Arlib.MarkovChains

end

section
/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Dirichlet form, the Poincaré inequality, and positive semidefiniteness

Where `Var_μ(f)` measures the *global* variation of `f`, the Dirichlet form
`ℰ_P(f)` measures its *local* variation along the edges of the transition graph
`(Ω, P)`.  The entire mixing-time theory is the comparison of the two: a chain
mixes quickly exactly when local variation controls global variation, which is
the Poincaré inequality `γ · Var_μ(f) ≤ ℰ_P(f)`.

* `dirichlet μ P f g` — the bilinear form `⟪f, (I - P) g⟫_μ`; the Dirichlet form
  proper is the quadratic case `dirichlet μ P f f`.
* `sum_pair_sq` — the workhorse: for a *stationary* `μ` and any `s : ℝ`,
  `∑ x, ∑ y, μ x * P x y * (f x + s * f y) ^ 2 = (1 + s²)⟪f,f⟫ + 2s⟪f, Pf⟫`.
  Specialising to `s = -1` gives the pair form of the Dirichlet form, and to
  `s = 1` the lower bound `-⟪f,f⟫ ≤ ⟪f, Pf⟫`.  Both signs matter: one says the
  chain is a contraction, the other that it cannot overshoot.
* `dirichlet_self_eq_pair` — `ℰ_P(f) = ½ ∑_{x,y} μ(x) P(x,y) (f x - f y)²`, the
  paper's definition, here a theorem.
* `SpectralGapAtLeast μ P γ` — the Poincaré inequality.  Following the source
  monograph we take this *as* the definition of the spectral gap: for reversible
  chains it agrees with `1 - λ₂`, and for non-reversible ones it is the right
  notion anyway (the "Poincaré constant"), so no eigenvalue is ever needed.
* `NonnegDefinite μ P` — `0 ≤ ⟪f, P f⟫_μ` for all `f`, the PSD condition.  This
  is what upgrades the spectral gap to the *absolute* spectral gap, and hence
  what makes the gap control the decay of variance; see
  `Arlib.MarkovChains.Techniques.SpectralGap`.

The pay-off proved here is `ip_act_le_of_gap`: on a mean-zero function a chain
with gap `γ` which is PSD satisfies `|⟪f, P f⟫_μ| ≤ (1 - γ) ⟪f, f⟫_μ`, the
two-sided bound that drives everything downstream.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/


namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The Dirichlet form -/



theorem dirichlet_apply (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    dirichlet μ P f g = ip μ f g - ip μ f (P.act g) := rfl

/-! ## The pair expansion

Everything about the Dirichlet form flows from a single computation: expanding
`∑_{x,y} μ(x) P(x,y) (f x + s · f y)²` for a stationary `μ`.  The `f x²` term is
resummed with `∑_y P x y = 1`, the `f y²` term with stationarity, and the cross
term is `⟪f, P f⟫_μ` on the nose. -/







/-! ## Two-sided control of `⟪f, P f⟫_μ`

A stochastic kernel is a contraction on `L²(μ)`: taking `s = -1` above bounds
`⟪f, P f⟫_μ` from above by `⟪f, f⟫_μ`, and taking `s = 1` bounds it from below
by `-⟪f, f⟫_μ`.  These are the elementary substitutes for "all eigenvalues lie
in `[-1, 1]`". -/







/-! ## Symmetry and bilinearity -/

/-- `⟪f, P g⟫_μ = ∑_x ∑_y μ(x)·P(x,y)·f(x)·g(y)`: the inner product against the
action of a kernel, written so that the detailed-balance cell `μ(x)·P(x,y)`
occurs as a subterm. -/
theorem ip_act_eq_sum_sum (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ∑ x, ∑ y, μ x * P x y * (f x * g y) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [FinKernel.act, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **Reversibility is exactly self-adjointness**: `⟪f, P g⟫_μ = ⟪g, P f⟫_μ`. -/
theorem ip_act_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (f g : Ω → ℝ) :
    ip μ f (P.act g) = ip μ g (P.act f) := by
  rw [ip_act_eq_sum_sum μ P f g, ip_act_eq_sum_sum μ P g f, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [h x y]; ring

/-- For a reversible chain the Dirichlet form is symmetric. -/
theorem dirichlet_comm {μ : FinDist Ω} {P : FinChain Ω} (h : Reversible μ P) (f g : Ω → ℝ) :
    dirichlet μ P f g = dirichlet μ P g f := by
  rw [dirichlet_apply, dirichlet_apply, ip_comm μ f g, ip_act_comm h f g]





/-! ## The spectral gap -/









/-! ## Positive semidefinite chains

A chain is *positive semidefinite* when `0 ≤ ⟪f, P f⟫_μ` for every `f` — the
elementary rendering of "all eigenvalues are nonnegative".  Heat-bath block
dynamics (in particular the Glauber dynamics) are PSD, and it is exactly this
that makes the spectral gap equal to the *absolute* spectral gap and hence makes
the gap control the decay of variance. -/





end Arlib.MarkovChains

end
set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic
end CountingMatroid.Analysis.PositiveTimeTraceHarmonic
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- PAPER: main.tex:1056-1058
Symmetry of the underlying Dirichlet form gives detailed balance of the
positive-time trace at boundary states, including zero stationary weights. -/
theorem solution (μ : FinDist Ω) (P : FinChain Ω)
    (hrev : Reversible μ P) (A : Finset Ω) (x y : Ω)
    (hx : x ∈ A) (hy : y ∈ A) :
    μ x * (uncappedReturn P A).entry x y =
      μ y * (uncappedReturn P A).entry y x := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  let f : Ω → ℝ := fun z => if z = x then 1 else 0
  let g : Ω → ℝ := fun z => if z = y then 1 else 0
  have hfg := dirichlet_comm hrev (harmonicExtension P A f) (harmonicExtension P A g)
  rw [harmonic_extension_energy, harmonic_extension_energy] at hfg
  have hleft : (∑ z ∈ A, μ z * f z *
      (g z - ∑ w, (uncappedReturn P A).entry z w * g w)) =
      - (μ x * (uncappedReturn P A).entry x y) := by
    simp [f, g, hx, hxy]
  have hright : (∑ z ∈ A, μ z * g z *
      (f z - ∑ w, (uncappedReturn P A).entry z w * f w)) =
      - (μ y * (uncappedReturn P A).entry y x) := by
    simp [f, g, hy, (Ne.symm hxy)]
  rw [hleft, hright] at hfg
  exact neg_injective hfg
