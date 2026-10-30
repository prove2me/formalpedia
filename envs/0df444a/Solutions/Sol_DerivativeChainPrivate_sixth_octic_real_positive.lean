-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_octic_real_positive
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:15:06.580958+00:00
-- url     : https://prove2.me/submissions/0fc67bf7-6aa7-41ec-a8aa-1a6be87cb6cd

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (x : ℝ) (hx : |x|≤3/10) :
    0<1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
      (2088025/1019304)*x^4+(35496425/33637032)*x^5 := by
  have ha : 0≤x+3/10 := by linarith [(abs_le.mp hx).1]
  have hb : 0≤3/10-x := by linarith [(abs_le.mp hx).2]
  have he :
      1-(2210/363)*x+(27455/2178)*x^2-(859775/84942)*x^3+
        (2088025/1019304)*x^4+(35496425/33637032)*x^5 =
      1/100+(58667832325/1076385024)*(3/10-x)^5+
        (155776763875/1076385024)*(x+3/10)*(3/10-x)^4+
        (74367210625/538192512)*(x+3/10)^2*(3/10-x)^3+
        (31723394875/538192512)*(x+3/10)^3*(3/10-x)^2+
        (11293419625/1076385024)*(x+3/10)^4*(3/10-x)+
        (608005175/1076385024)*(x+3/10)^5 := by ring
  rw [he]
  positivity
