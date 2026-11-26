-- Prove2me | solution 1 for CurrentTwoFormEstimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:00:25.693779+00:00
-- url     : https://prove2.me/submissions/6ed037dd-a936-4f7c-89e2-ad402098631e

import Definitions.Def_Tablet_CurrentFormAddF
import Definitions.Def_Tablet_CurrentFormAddPi
import Definitions.Def_Tablet_PiBoundsF
import Definitions.Def_Tablet_PiBoundsPi
import Definitions.Def_Tablet_psi
import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentTwoFormEstimate
import Theorems.Thm_CurrentFormAddF
import Theorems.Thm_CurrentFormAddPi
import Theorems.Thm_PiBoundsF
import Theorems.Thm_PiBoundsPi


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (γ : Curve E) (m : ℕ) (hm : 1 ≤ m)
    (Q : Finset E) (hQne : Q.Nonempty) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (ω ωk ωkj : Form1 E)
    (hfk : ωkj.f = ωk.f) (hpik : ωk.pi = ω.pi)
    (hfB : (ω.fBound : ℝ) ≤ C) (hfBk : (ωk.fBound : ℝ) ≤ C)
    (hfL : (ω.fLip : ℝ) ≤ C) (hfLk : (ωk.fLip : ℝ) ≤ C)
    (hpL : (ω.piLip : ℝ) ≤ C) (hpLk : (ωk.piLip : ℝ) ≤ C) (hpLkj : (ωkj.piLip : ℝ) ≤ C)
    (hQf : ∀ q ∈ Q, |ω.f q - ωk.f q| ≤ ε)
    (hQpi : ∀ q ∈ Q, |ω.pi q - ωkj.pi q| ≤ ε) :
    |curveCurrent γ ω - curveCurrent γ ωkj| ≤ psiTilde m Q ε C γ + psi m Q ε C γ := by
-- BODY
  set D1 : Form1 E :=
    { f := fun x => ω.f x - ωk.f x,
      fBound := ω.fBound + ωk.fBound,
      f_bounded := fun x => (abs_sub _ _).trans
        (by push_cast; exact add_le_add (ω.f_bounded x) (ωk.f_bounded x)),
      fLip := ω.fLip + ωk.fLip,
      f_lipschitz := ω.f_lipschitz.sub ωk.f_lipschitz,
      pi := ω.pi, piLip := ω.piLip, pi_lipschitz := ω.pi_lipschitz } with hD1
  set D2 : Form1 E :=
    { f := ωk.f, fBound := ωk.fBound, f_bounded := ωk.f_bounded,
      fLip := ωk.fLip, f_lipschitz := ωk.f_lipschitz,
      pi := fun x => ωk.pi x - ωkj.pi x,
      piLip := ωk.piLip + ωkj.piLip,
      pi_lipschitz := ωk.pi_lipschitz.sub ωkj.pi_lipschitz } with hD2
  have hAF : curveCurrent γ ω = curveCurrent γ D1 + curveCurrent γ ωk :=
    CurrentFormAddF γ D1 ωk ω rfl hpik
      (fun x => by show ω.f x = (ω.f x - ωk.f x) + ωk.f x; ring)
  have hAPi : curveCurrent γ ωk = curveCurrent γ D2 + curveCurrent γ ωkj :=
    CurrentFormAddPi γ D2 ωkj ωk rfl hfk
      (fun x => by show ωk.pi x = (ωk.pi x - ωkj.pi x) + ωkj.pi x; ring)
  have hBF : |curveCurrent γ D1| ≤ psiTilde m Q ε C γ :=
    PiBoundsF γ m hm Q hQne ε C hε hC ω ωk hfB hfBk hfL hfLk hpL hQf
  have hQpi' : ∀ q ∈ Q, |ωk.pi q - ωkj.pi q| ≤ ε := by
    intro q hq; rw [hpik]; exact hQpi q hq
  have hBPi : |curveCurrent γ D2| ≤ psi m Q ε C γ :=
    PiBoundsPi γ m hm Q hQne ε C hε hC ωk ωkj hfBk hfLk hpLk hpLkj hQpi'
  have hsplit : curveCurrent γ ω - curveCurrent γ ωkj = curveCurrent γ D1 + curveCurrent γ D2 := by
    rw [hAF, hAPi]; ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hBF hBPi)
